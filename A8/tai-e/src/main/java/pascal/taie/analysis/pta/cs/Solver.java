/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public CSCallGraph getCallGraph(){
        return callGraph;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            Context c = csMethod.getContext();
            csMethod.getMethod().getIR().forEach(stmt -> {
                if (stmt instanceof New newStmt) {
                    // x = new T();
                    // 你可以使用 HeapModel 的 getObj(New) 方法来获得与它对应的抽象对象（即 Obj）。因为我们采用了第 8 讲课件第 44 页中介绍的创建点抽象，所以该方法为每个 New 语句返回一个唯一的抽象对象。
                    Var x = newStmt.getLValue();
                    Obj newT = heapModel.getObj(newStmt);
                    // 堆上下文不一定就使用方法的上下文,需要用 ContextSelector选择
                    Context heapContext = contextSelector.selectHeapContext(csMethod, newT);
                    CSObj csObj = csManager.getCSObj(heapContext, newT);
                    workList.addEntry(csManager.getCSVar(c, x), PointsToSetFactory.make(csObj));
                } else if (stmt instanceof Copy copyStmt) {
                    // x = y;
                    Var x = copyStmt.getRValue();
                    Var y = copyStmt.getLValue();
                    addPFGEdge(csManager.getCSVar(c, x), csManager.getCSVar(c, y)); // source, target
                } else if (stmt instanceof StoreField storeFieldStmt) {
                    // x.f = y;
                    JField f = storeFieldStmt.getFieldRef().resolve();
                    Var y = storeFieldStmt.getRValue();
                    // 这两个类也提供了 isStatic() 方法来检查一个 LoadField/StoreField 语句是 load/store 静态字段还是实例字段
                    // 静态字段的处理很简单：我们只需要在静态字段和变量之间传值。TODO 怎么没有静态变量之间的操作
                    if (f.isStatic()) {
                        addPFGEdge(csManager.getCSVar(c, y), csManager.getStaticField(f)); // source, target
                    }
                } else if (stmt instanceof LoadField loadFieldStmt) {
                    // y = x.f;
                    // TODO resolve干了什么?
                    JField f = loadFieldStmt.getFieldRef().resolve();
                    Var y = loadFieldStmt.getLValue();
                    if (f.isStatic()) {
                        addPFGEdge(csManager.getStaticField(f), csManager.getCSVar(c, y));
                    }
                } else if (stmt instanceof Invoke l) {
                    // 只处理 static调用,因为 static调用不需要 receive object
                    if (l.isStatic()) {
                        // r = T.m(a1,...,an)
                        MethodRef methodRef = l.getMethodRef();
                        JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
                        // Select(c,l,c':oi)
                        // 根据调用点的信息(上下文,接受对象)选择目标方法的上下文 ct
                        CSCallSite csCallSite = csManager.getCSCallSite(c, l);
                        Context ct = contextSelector.selectContext(csCallSite, m);
                        CSMethod ctMethod = csManager.getCSMethod(ct, m);
                        // 检查调用边是否已经添加过
                        // TODO 视频中有提到为什么会重复添加 (p10 1:03)
                        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(l), csCallSite, ctMethod))) {
                            addReachable(ctMethod);
                            Set<Obj> taints = taintAnalysis.getSourceTaintObjs(m, l);
                            addCallEdge(null, ctMethod, l, c, taints);
                        }
                    }
                }
            });
        }
    }

    private void addCallEdge(CSVar cx, CSMethod m, Invoke invokeStmt, Context c, Set<Obj> taints) {
        Context ct = m.getContext();
        PointsToSet pt_c_x = cx != null ? cx.getPointsToSet() : null;
        // add return values -> r
        Var r = invokeStmt.getLValue(); // @Nullable
        CSVar cr = r != null ? csManager.getCSVar(c, r) : null;
        PointsToSet pt_c_r = cr != null ? cr.getPointsToSet() : null;

        if (pt_c_r != null) {
            m.getMethod().getIR().getReturnVars().forEach(returnVar -> {
                // ct:m_ret -> c:r
                addPFGEdge(csManager.getCSVar(ct, returnVar), cr);
            });
            // TODO add source taints
            taints.forEach(obj -> {
                // TODO 应该加入workList?
                workList.addEntry(cr, PointsToSetFactory.make(csManager.getCSObj(taintAnalysis.getEmptyContext(), obj)));
                // pt_c_r.addObject(csManager.getCSObj(taintAnalysis.getEmptyContext(), obj));
            });
            // TODO add base-to-result
            List<Type> base2resultTypes = taintAnalysis.getTransfer(m.getMethod(), taintAnalysis.getBase(), taintAnalysis.getResult());
            assert base2resultTypes.size() <= 1 : "base2resultTypes.size() <= 1 fail";
            if (pt_c_x != null && !base2resultTypes.isEmpty()) {
                pt_c_x.forEach(csObj -> {
                    Invoke j = taintAnalysis.getSourceCall(csObj.getObject()); // j
                    if (j == null) {
                        return;
                    }
                    add(cr, base2resultTypes, j);
                });
            }
        }
        // add actuals -> params
        List<Var> params = m.getMethod().getIR().getParams();
        List<Var> actuals = invokeStmt.getRValue().getArgs();
        for (int i = 0; i < params.size(); i++) {
            CSVar cai = csManager.getCSVar(c, actuals.get(i));
            CSVar cpi = csManager.getCSVar(ct, params.get(i));
            // c:ai -> ct:pi
            addPFGEdge(cai, cpi);

            List<Type> arg2baseTypes = taintAnalysis.getTransfer(m.getMethod(), i, taintAnalysis.getBase());
            assert arg2baseTypes.size() <= 1 : "arg2baseTypes.size() <= 1 fail";
            List<Type> arg2resultTypes = taintAnalysis.getTransfer(m.getMethod(), i, taintAnalysis.getResult());
            assert arg2resultTypes.size() <= 1 : "arg2resultTypes <= 1 fail";

            PointsToSet pt_c_ai = cai.getPointsToSet();
            pt_c_ai.forEach(csObj -> {
                Invoke j = taintAnalysis.getSourceCall(csObj.getObject()); // j
                if (j == null) {
                    return;
                }
                // TODO add arg-to-base
                add(cx, arg2baseTypes, j);
                // TODO add arg-to-result
                add(cr, arg2resultTypes, j);
            });
        }
    }

    private void add(CSVar csVar, List<Type> types, Invoke j) {
        if (!types.isEmpty() && csVar != null) {
            Type u = types.get(0);
            Obj t_j_u = taintAnalysis.getTaintObj(j, u);
            CSObj cs_t_j_u = csManager.getCSObj(taintAnalysis.getEmptyContext(), t_j_u);
            workList.addEntry(csVar, PointsToSetFactory.make(cs_t_j_u));
            // pt.addObject(
            //         csManager.getCSObj(
            //                 taintAnalysis.getEmptyContext(), // []
            //                 taintAnalysis.getTaint(j, u)) // t_j_u
            // );
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        // true if this PFG changed as a result of the call
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                // TODO 这里需要拷贝吗
                workList.addEntry(target, pts);
            }
        }
    }

    private <T> Set<T> getSetDifference(Set<T> x, Set<T> y) {
        Set<T> diff = new HashSet<>(x);
        diff.removeAll(y);
        return diff;
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            // 1. remove <n,pts> from WL
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            // 2. Δ
            PointsToSet delta = propagate(n, pts);
            // 3. if n represents a variable x then
            if (n instanceof CSVar cx) {
                Var x = cx.getVar();
                Context c = cx.getContext();
                // 3.1 foreach oi in Δ do
                // TODO taint object 和 普通 object 需要分开处理吗 ?
                delta.getObjects().forEach(csoi -> {
                    if (taintAnalysis.isTaintObject(csoi.getObject())) {
                        Invoke j = taintAnalysis.getSourceCall(csoi.getObject()); // j
                        assert j != null : "j != null fail";

                        x.getMethod().getIR().forEach(stmt -> {
                            if (stmt instanceof Invoke invoke) {
                                Var r = invoke.getLValue(); // result of the invocation, @Nullable
                                CSVar cr;
                                if (r != null) {
                                    cr = csManager.getCSVar(c, r);
                                } else {
                                    cr = null;
                                }
                                List<Var> args = invoke.getInvokeExp().getArgs();
                                if (invoke.isStatic()) {
                                    JMethod callee = resolveCallee(null, invoke);
                                    for (int i = 0; i < args.size(); i++) {
                                        Var var = args.get(i);
                                        if (var != x) {
                                            continue;
                                        }
                                        List<Type> arg2resultTypes = taintAnalysis.getTransfer(callee, i, taintAnalysis.getResult());
                                        assert arg2resultTypes.size() <= 1 : "arg2resultTypes <= 1 fail";

                                        // TODO add arg-to-result
                                        add(cr, arg2resultTypes, j);
                                    }
                                } else {
                                    InvokeInstanceExp instanceExp = (InvokeInstanceExp) invoke.getInvokeExp();
                                    Var base = instanceExp.getBase();
                                    CSVar csBase = csManager.getCSVar(c, base);
                                    PointsToSet basePt = csBase.getPointsToSet();
                                    basePt.forEach(csBaseObj -> {
                                        JMethod callee = resolveCallee(csBaseObj, invoke);
                                        if (base == x) {
                                            List<Type> base2resultTypes = taintAnalysis.getTransfer(callee, taintAnalysis.getBase(), taintAnalysis.getResult());
                                            assert base2resultTypes.size() <= 1 : "base2resultTypes.size() <= 1 fail";
                                            // TODO add base-to-result
                                            add(cr, base2resultTypes, j);
                                        }
                                        for (int i = 0; i < args.size(); i++) {
                                            Var var = args.get(i);
                                            if (var != x) {
                                                continue;
                                            }
                                            List<Type> arg2baseTypes = taintAnalysis.getTransfer(callee, i, taintAnalysis.getBase());
                                            assert arg2baseTypes.size() <= 1 : "arg2baseTypes.size() <= 1 fail";
                                            List<Type> arg2resultTypes = taintAnalysis.getTransfer(callee, i, taintAnalysis.getResult());
                                            assert arg2resultTypes.size() <= 1 : "arg2resultTypes <= 1 fail";

                                            // TODO 可能重复添加?但没关系?
                                            // TODO add arg-to-base
                                            add(csBase, arg2baseTypes, j);
                                            // TODO add arg-to-result
                                            add(cr, arg2resultTypes, j);
                                        }
                                    });
                                }
                            }
                        });
                        return;
                    }
                    // 3.1.1 foreach x.f = y in S do
                    x.getStoreFields().forEach(storeField -> {
                        Var y = storeField.getRValue();
                        JField f = storeField.getFieldRef().resolve();
                        addPFGEdge(csManager.getCSVar(c, y), csManager.getInstanceField(csoi, f));
                    });
                    // 3.1.1 foreach y = x.f in S do
                    x.getLoadFields().forEach(loadField -> {
                        Var y = loadField.getLValue();
                        JField f = loadField.getFieldRef().resolve();
                        addPFGEdge(csManager.getInstanceField(csoi, f), csManager.getCSVar(c, y));
                    });
                    // TODO 不要忘记在这个方法中处理数组 loads/stores。
                    x.getStoreArrays().forEach(storeArray -> {
                        Var y = storeArray.getRValue();
                        addPFGEdge(csManager.getCSVar(c, y), csManager.getArrayIndex(csoi));
                    });
                    x.getLoadArrays().forEach(loadArray -> {
                        Var y = loadArray.getLValue();
                        addPFGEdge(csManager.getArrayIndex(csoi), csManager.getCSVar(c, y));
                    });
                    processCall(cx, csoi); // x.f.someCall ?
                    // TODO add invoke statement use this variable ?
                    // x.getMethod().getIR().forEach(stmt -> {
                    //     if (stmt instanceof Invoke invoke) {
                    //         List<Var> args = invoke.getInvokeExp().getArgs();
                    //         args.forEach(var -> {
                    //
                    //         });
                    //     }
                    // });
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer n, PointsToSet pts) {
        // TODO - finish me
        if (pts.isEmpty()) {
            return PointsToSetFactory.make();
        }
        PointsToSet ptn = n.getPointsToSet();
        Set<CSObj> difference = getSetDifference(pts.getObjects(), ptn.getObjects());

        PointsToSet delta = PointsToSetFactory.make();
        difference.forEach(obj -> {
            ptn.addObject(obj);
            delta.addObject(obj);
        });

        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(n).forEach(s -> {
                workList.addEntry(s, delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param cx    the receiver variable
     * @param csoi set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar cx, CSObj csoi) {
        // TODO - finish me
        Context c = cx.getContext();
        Var x = cx.getVar();
        x.getInvokes().forEach(l -> {
            if (l.isStatic()) { // static已经处理过了
                return;
            }
            // 你将在这个方法中处理所有种类的实例方法调用，即虚调用、接口调用和特殊调用。
            // 处理接口调用和特殊调用的逻辑与处理虚调用的逻辑完全相同（你在课上已经学过）。
            // 你也可以使用上面提到的 resolveCallee() （代替算法中的 Dispatch）来解析所有种类的实例方法调用，
            // 即虚调用、接口调用和特殊调用。
            JMethod m = resolveCallee(csoi, l);
            // TODO m_this 怎么表示? 解决方法:调试到这里,查看m所有属性
            Var m_this = m.getIR().getThis();
            CSCallSite csCallSite = csManager.getCSCallSite(c, l);
            // ct = Select(c,l,c':oi)
            Context ct = contextSelector.selectContext(csCallSite, csoi, m); // selectContext(csCallSite, m) -> selectContext(csCallSite, csoi, m)
            CSMethod ctMethod = csManager.getCSMethod(ct, m);
            workList.addEntry(csManager.getCSVar(ct, m_this), PointsToSetFactory.make(csoi));

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(l), csCallSite, ctMethod))) { // true if the call graph changed as a result of the call
                // 添加边成功,添加可达方法
                addReachable(ctMethod);
                // TODO 只添加一次,和那个m_this类比?
                Set<Obj> taints = taintAnalysis.getSourceTaintObjs(m, l);
                addCallEdge(cx, ctMethod, l, c, taints);
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
