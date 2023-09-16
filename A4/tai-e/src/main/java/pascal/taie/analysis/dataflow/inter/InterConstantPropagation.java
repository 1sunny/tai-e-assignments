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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    // public boolean transferNode(Node node, Fact in, Fact out) {
    //     if (icfg.isCallSite(node)) {
    //         return transferCallNode(node, in, out);
    //     } else {
    //         return transferNonCallNode(node, in, out);
    //     }
    // }
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 不需要管左边定义的变量,会在调用函数返回的Return Edge被汇合
        CPFact copy_out = out.copy();
        out.clear();
        in.forEach(out::update);
        return !copy_out.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    // 在实现 transfer*Edge() 方法的时候，不应该修改第二个参数，也就是该边的源节点的 OUT fact。
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact copy_out = out.copy();
        edge.getSource().getDef().ifPresent(lValue -> copy_out.remove((Var) lValue));
        return copy_out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact fact = new CPFact();
        // TODO
        List<RValue> actual = edge.getSource().getUses();
        List<Var> params = edge.getCallee().getIR().getParams();
        // actual里面会有 1.receive obj(如果有) 2.参数 3.调用方法InvokeExp
        assert actual.size() <= params.size() + 2 : "actual.size() <= params.size() + 2 fail";
        int offset = 0;
        if (actual.size() == params.size() + 2) {
            offset = 1;
        }
        for (int i = 0; i < params.size(); i++) {
            // 将参数设置为调用点给定的实参
            fact.update(params.get(i), callSiteOut.get((Var) actual.get(i + offset)));
        }
        return fact;
    }

    /**
     * edge transfer 函数将被调用方法的返回值传递给调用点等号左侧的变量。
     * 具体来说，它从被调用方法的 exit 节点的 OUT fact 中获取返回值（可能有多个，你需要思考一下该怎么处理）
     * @param edge
     * @param returnOut
     * @return 一个将调用点等号左侧的变量映射到返回值的 fact
     */
    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact fact = new CPFact();
        Optional<LValue> def = edge.getCallSite().getDef();
        if (def.isPresent()) {
            /**
             * Each method in ICFG has only one exit, but it may have multiple return
             * statements. This API returns all returned variables. E.g., for the
             * return edges starting from the exit of method:
             * <pre>
             * int foo(...) {
             *     if (...) {
             *         return x;
             *     } else {
             *         return y;
             *     }
             * }
             * </pre>
             * this API returns [x, y].
             *
             * @return the variables that hold the return values.
             */
            Collection<Var> returnVars = edge.getReturnVars();
            // assert returnVars.size() == 1 : "returnVars.size() == 1 fail";
            assert returnVars.size() >= 1 : "returnVars.size() >= 1 fail";
            Value returnValue = Value.getUndef();
            for (Var var : returnVars) {
                returnValue = cp.meetValue(returnValue, returnOut.get(var));
            }
            // 设置调用点语句左边定义的变量值为函数的返回值(Exit nop的OUT里面)
            fact.update((Var) def.get(), returnValue);
            return fact;
        }
        return fact;
    }
}
