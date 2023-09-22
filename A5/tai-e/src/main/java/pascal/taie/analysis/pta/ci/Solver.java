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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.*;
import pascal.taie.language.type.Type;

import java.util.*;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // TODO LoadArray/StoreArray里面如果也是静态的需要考虑吗?
        // public static A[] a;
        // main:
        // a = new A[2];
        // a[0] = new A();
        // 会被转化为以下形式,静态数组会用 temp$1代替
        // temp$1 = <My: A[] a>;
        // temp$3 = new A;
        // invokespecial temp$3.<A: void <init>()>();
        // temp$2 = 0;
        // temp$1[temp$2] = temp$3;


        // TODO 类的字段间(非静态,静态)的赋值为什么没有体现?
        // 类的非静态字段属于 this对象, init函数里面会初始化类的非静态字段
        // 假如有非静态字段 a和 b, a = b会被转化为 temp$0 = b; a = temp$0;

        // 静态字段在声明时就初始化不会被加入指针集,clinit函数没被调用,不知道为什么...
        // 1: class A {
        // 2:      static int one = 1; // field initializer
        // 3:      static int two;
        // 4:
        // 5:      static { // static initializer
        // 6:          one = 1; // generated for field initializer at line 2
        // 7:          two = 2;
        // 8:      }
        // 9:  }
        // 具体而言，第 2 行的静态字段初始化会被编译为一个静态初始化块（5 - 8 行）中的 store 语句（第 6 行），\
        // 因此仅处理静态初始化块即可。然而，本次作业中的 call graph builder 并不处理静态初始化块（但在 Tai-e 中它们会被正确处理），
        // 因此这些 store 语句在 ICFG 上是不可达的。简单起见，我们在本次作业中忽略字段的初始化和静态初始化块。

        // 在函数中赋值会通过和非静态字段一样的处理方式完成

        // TODO addReachable x = y addEdge可以放到analysis?

        // TODO 不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用。
        if (callGraph.addReachableMethod(method)) {
            // default Iterator<Stmt> iterator() {
            //     return getStmts().iterator();
            // }
            method.getIR().forEach(stmt -> {
                if (stmt instanceof New newStmt) {
                    // x = new T();
                    // 你可以使用 HeapModel 的 getObj(New) 方法来获得与它对应的抽象对象（即 Obj）。因为我们采用了第 8 讲课件第 44 页中介绍的创建点抽象，所以该方法为每个 New 语句返回一个唯一的抽象对象。
                    Var x = newStmt.getLValue();
                    Obj newT = heapModel.getObj(newStmt);
                    workList.addEntry(pointerFlowGraph.getVarPtr(x), new PointsToSet(newT));
                } else if (stmt instanceof Copy copyStmt) {
                    // x = y;
                    Var x = copyStmt.getRValue();
                    Var y = copyStmt.getLValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(x), pointerFlowGraph.getVarPtr(y)); // source, target
                } else if (stmt instanceof StoreField storeFieldStmt) {
                    // x.f = y;
                    JField f = storeFieldStmt.getFieldRef().resolve();
                    Var y = storeFieldStmt.getRValue();
                    // 这两个类也提供了 isStatic() 方法来检查一个 LoadField/StoreField 语句是 load/store 静态字段还是实例字段
                    // 静态字段的处理很简单：我们只需要在静态字段和变量之间传值。TODO 怎么没有静态变量之间的操作
                    if (f.isStatic()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(f)); // source, target
                    }
                } else if (stmt instanceof LoadField loadFieldStmt) {
                    // y = x.f;
                    // TODO resolve干了什么?
                    JField f = loadFieldStmt.getFieldRef().resolve();
                    Var y = loadFieldStmt.getLValue();
                    if (f.isStatic()) {
                        addPFGEdge(pointerFlowGraph.getStaticField(f), pointerFlowGraph.getVarPtr(y));
                    }
                } else if (stmt instanceof Invoke l) {
                    // 只处理 static调用,因为 static调用不需要 receive object
                    if (l.isStatic()) {
                        // r = T.m(a1,...,an)
                        MethodRef methodRef = l.getMethodRef();
                        JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
                        // 检查调用边是否已经添加过
                        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(l), l, m))) {
                            addReachable(m);
                            addCallEdge(m, l);
                        }
                    }
                }
                // 数组也是静态的呢?
            });
        }
    }

    private void addCallEdge(JMethod m, Invoke invokeStmt) {
        // add actuals -> params
        List<Var> params = m.getIR().getParams();
        List<Var> actuals = invokeStmt.getRValue().getArgs();
        for (int i = 0; i < params.size(); i++) {
            addPFGEdge(pointerFlowGraph.getVarPtr(actuals.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
        }
        // add return values -> r
        Var lValue = invokeStmt.getLValue(); // @Nullable
        if (lValue != null) {
            m.getIR().getReturnVars().forEach(returnVar -> {
                addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(lValue));
            });
        }
    }
    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        // Modifier 'public' is redundant for interface members
        public Void visit(New stmt) {
            return visitDefault(stmt);
        }

        public Void visit(AssignLiteral stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Copy stmt) {
            return visitDefault(stmt);
        }

        public Void visit(LoadArray stmt) {
            return visitDefault(stmt);
        }

        public Void visit(StoreArray stmt) {
            return visitDefault(stmt);
        }

        public Void visit(LoadField stmt) {
            return visitDefault(stmt);
        }

        public Void visit(StoreField stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Binary stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Unary stmt) {
            return visitDefault(stmt);
        }

        public Void visit(InstanceOf stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Cast stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Goto stmt) {
            return visitDefault(stmt);
        }

        public Void visit(If stmt) {
            return visitDefault(stmt);
        }

        public Void visit(TableSwitch stmt) {
            return visitDefault(stmt);
        }

        public Void visit(LookupSwitch stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Invoke stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Return stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Throw stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Catch stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Monitor stmt) {
            return visitDefault(stmt);
        }

        public Void visit(Nop stmt) {
            return visitDefault(stmt);
        }
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
            if (n instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                // 3.1 foreach oi in Δ do
                delta.getObjects().forEach(oi -> {
                    // 3.1.1 foreach x.f = y in S do
                    x.getStoreFields().forEach(storeField -> {
                        Var y = storeField.getRValue();
                        JField f = storeField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getInstanceField(oi, f));
                    });
                    // 3.1.1 foreach y = x.f in S do
                    x.getLoadFields().forEach(loadField -> {
                        Var y = loadField.getLValue();
                        JField f = loadField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getInstanceField(oi, f), pointerFlowGraph.getVarPtr(y));
                    });
                    // TODO 不要忘记在这个方法中处理数组 loads/stores。
                    x.getStoreArrays().forEach(storeArray -> {
                        Var y = storeArray.getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getArrayIndex(oi));
                    });
                    x.getLoadArrays().forEach(loadArray -> {
                        Var y = loadArray.getLValue();
                        addPFGEdge(pointerFlowGraph.getArrayIndex(oi), pointerFlowGraph.getVarPtr(y));
                    });
                    processCall(varPtr.getVar(), oi);
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
            return new PointsToSet();
        }
        PointsToSet ptn = n.getPointsToSet();
        Set<Obj> difference = getSetDifference(pts.getObjects(), ptn.getObjects());

        PointsToSet delta = new PointsToSet();
        difference.forEach(obj -> {
            ptn.addObject(obj);
            delta.addObject(obj);
        });

        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(n).forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param x the variable that holds receiver objects
     * @param oi a new discovered object pointed by the variable.
     */
    private void processCall(Var x, Obj oi) {
        // TODO - finish me
        x.getInvokes().forEach(l -> {
            if (l.isStatic()) { // static已经处理过了
                return;
            }
            // 你将在这个方法中处理所有种类的实例方法调用，即虚调用、接口调用和特殊调用。
            // 处理接口调用和特殊调用的逻辑与处理虚调用的逻辑完全相同（你在课上已经学过）。
            // 你也可以使用上面提到的 resolveCallee() （代替算法中的 Dispatch）来解析所有种类的实例方法调用，
            // 即虚调用、接口调用和特殊调用。
            JMethod m = resolveCallee(oi, l);
            // TODO m_this 怎么表示? 解决方法:调试到这里,查看m所有属性
            Var m_this = m.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(m_this), new PointsToSet(oi));

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(l), l, m))) { // true if the call graph changed as a result of the call
                // 添加边成功,添加可达方法
                addReachable(m);
                addCallEdge(m, l);
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
