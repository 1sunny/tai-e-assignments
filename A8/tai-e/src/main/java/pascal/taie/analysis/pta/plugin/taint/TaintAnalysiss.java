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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Stream;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    // 我们也初始化了 TaintManager 对象并将其保存在了 manager 字段中，你可以通过它来管理污点对象
    private final TaintManager manager;

    // 在 TaintAnalysiss 的构造函数中，我们已经给出了解析配置文件的代码，
    // 并把解析的结果保存在了 config 字段中，你可以直接使用它
    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Set<Obj> getSourceTaintObjs(JMethod method, Invoke l) {
        Set<Obj> result = new HashSet<>();
        for (Source source : config.getSources()) {
            if (source.method() == method) {
                result.add(manager.makeTaint(l, source.type()));
            }
        }
        return result;
    }

    public Obj getTaintObj(Invoke l, Type type) {
        return manager.makeTaint(l, type);
    }

    public List<Type> getTransfer(JMethod method, int from, int to) {
        List<Type> result = new ArrayList<>();
        Set<TaintTransfer> transfers = config.getTransfers();
        transfers.forEach(taintTransfer -> {
            if (taintTransfer.method() == method
             && taintTransfer.from() == from
             && taintTransfer.to() == to) {
                result.add(taintTransfer.type());
            }
        });
        return result;
    }

    public boolean isTaintObject(Obj obj) {
        return manager.isTaint(obj);
    }

    public Invoke getSourceCall(Obj obj) {
        if (isTaintObject(obj)) {
            return manager.getSourceCall(obj);
        }
        return null;
    }

    public Context getEmptyContext() {
        return emptyContext;
    }

    public int getBase() {
        return TaintTransfer.BASE;
    }

    public int getResult() {
        return TaintTransfer.RESULT;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    // 返回一个集合，其中包含污点分析检测到的所有 taint flows。
    // 提示：你可以在这个方法中实现处理 sink 的规则
    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        Stream<Edge<CSCallSite, CSMethod>> edges = solver.getCallGraph().edges();
        edges.forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            Invoke l = csCallSite.getCallSite(); // l
            Context c = csCallSite.getContext();
            MethodRef methodRef = l.getMethodRef();
            JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
            config.getSinks().forEach(sink -> {
                if (sink.method() != m) {
                    return;
                }
                int index = sink.index();
                if (index >= 0) {
                    assert m != null;
                    Var arg = l.getInvokeExp().getArg(index);
                    CSVar csVar = csManager.getCSVar(c, arg);
                    // CSVar csParam = csManager.getCSVar(c, m.getIR().getParam(index));
                    csVar.getPointsToSet().forEach(csObj -> {
                        Obj obj = csObj.getObject();
                        Invoke j = getSourceCall(obj);
                        if (j != null) {
                            taintFlows.add(new TaintFlow(j, l, index));
                        }
                    });
                }
            });
        });
        return taintFlows;
    }
}
