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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<Var, List<StoreField>> aliasStoreField;

    private Map<Var, List<LoadField>> aliasLoadField;

    private Map<Var, List<LoadArray>> aliasLoadArray;

    private Map<Var, List<StoreArray>> aliasStoreArray;

    // 这样做会丢失精度
    // class My {
    //     public static void main(String[] args) {
    //         A a1 = new B();
    //         a1.f = 111;
    //         B b1 = (B)a1;
    //         int x = b1.f;
    //     }
    // }
    // class A {
    //     int f;
    // }
    // class B extends A {
    //
    // }
    private <T> List<T> getStmtList(Var base, Map<Var, List<T>> map) {
        if (!map.containsKey(base)) {
            return List.of(); // ImmutableCollections.EMPTY_LIS
        }
        return map.get(base);
    }

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    // InterConstantPropagation 的 initialize() 方法会在求解器启动前被调用，
    // 它包含了获取 PointerAnalysisResult 的相关代码，如果你的实现中需要进行一些初始化操作，
    // 你可以考虑在该方法中进行。
    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        aliasLoadField = new HashMap<>();
        aliasStoreField = new HashMap<>();
        aliasLoadArray = new HashMap<>();
        aliasStoreArray = new HashMap<>();

        for (Var var : pta.getVars()) {
            aliasStoreField.put(var, new ArrayList<>());
            aliasLoadField.put(var, new ArrayList<>());
            aliasStoreArray.put(var, new ArrayList<>());
            aliasLoadArray.put(var, new ArrayList<>());
            for (Var other : pta.getVars()) {
                for (Obj obj : pta.getPointsToSet(var)) {
                    if (pta.getPointsToSet(other).contains(obj)) {
                        aliasStoreField.get(var).addAll(other.getStoreFields());
                        aliasLoadField.get(var).addAll(other.getLoadFields());
                        aliasLoadArray.get(var).addAll(other.getLoadArrays());
                        aliasStoreArray.get(var).addAll(other.getStoreArrays());
                        break;
                    }
                }
            }
        }
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

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 因为这是函数调用语句,不需要管左边定义的变量,定义的变量会在调用函数返回的Return Edge被汇合
        CPFact copy_out = out.copy();
        out.clear();
        in.forEach(out::update);
        return !copy_out.equals(out);
    }

    public Value evaluate(Exp exp, CPFact in) {
        /*
        // 该类提供了一系列查询指针分析结果的 API，你可以用它来计算别名信息。
        // 值得注意的是，该类分别提供对带上下文的分析结果的查询（例如 getPointsToSet(CSVar)），
        // 和对不带上下文的分析结果的查询（例如 getPointsToSet(Var)）。
        // 由于过程间常量传播不需要知道指针分析结果中的上下文信息，你应该使用不带上下文的指针分析结果。
        // (注：针对一个上下文敏感的指针分析的分析结果，Tai-e 通过将同一指针在不同上下文下的指针集合并，
        // 并将不同上下文下的同一堆对象合并为一个堆对象，来去除上下文敏感的指针分析的结果中的上下文信息。
        // 需要注意的是，虽然结果中没有上下文信息，但相比于非上下文敏感，该结果取得了上下文敏感所能带来的精度提升（是构建callGraph的进度提示？））

        // * Relevant statements of a variable, say v, which include:
        // * load field: x = v.f;
        // * store field: v.f = x;
        // * load array: x = v[i];
        // * store array: v[i] = x;
        // * invocation: v.f();
        // TODO 1.找到其它表达式，不是InstanceField，而是InstanceFieldAccess
        // TODO 2.找到所有别名，为什么别名一定会也是InstanceFieldAccess，而不会是Var
        // TODO 3.找到所有和别名相关的赋值语句
        */
        Value res;
        if (exp instanceof StaticFieldAccess staticFieldAccess) {
            res = Value.getUndef();
            for (Stmt stmt : icfg) {
                if (stmt instanceof StoreField storeField
                 && storeField.isStatic()
                 && storeField.getFieldRef().resolve() == staticFieldAccess.getFieldRef().resolve()) {
                    Value value = solver.getResult().getInFact(stmt).get(storeField.getRValue());
                    res = cp.meetValue(res, value);
                }
            }
        } else if (exp instanceof InstanceFieldAccess instanceFieldAccess) {
            res = Value.getUndef();
            Var base = instanceFieldAccess.getBase();

            List<StoreField> storeFields = getStmtList(base, aliasStoreField);

            for (StoreField storeField : storeFields) {
                FieldAccess fieldAccess = storeField.getFieldAccess();
                if (fieldAccess instanceof InstanceFieldAccess && fieldAccess.getFieldRef().resolve() == instanceFieldAccess.getFieldRef().resolve()) {
                    Value value = solver.getResult().getInFact(storeField).get(storeField.getRValue());
                    res = cp.meetValue(res, value);
                }
            }
        } else if (exp instanceof ArrayAccess arrayAccess) {
            res = Value.getUndef();
            Var base = arrayAccess.getBase();
            Value indexI = in.get(arrayAccess.getIndex());

            List<StoreArray> storeArrays = getStmtList(base, aliasStoreArray);
            for (StoreArray storeArray : storeArrays) {
                ArrayAccess aliasArrayAccess = storeArray.getArrayAccess();
                Value indexJ = solver.getResult().getInFact(storeArray).get(aliasArrayAccess.getIndex());

                if (isArrayIndexAlias(indexI, indexJ)) { // found alias
                    Value value = solver.getResult().getInFact(storeArray).get(storeArray.getRValue());
                    res = cp.meetValue(res, value);
                }
            }
        } else {
            res = Value.getNAC();
        }
        return res;
    }

    private boolean isArrayIndexAlias(Value indexI, Value indexJ) {
        boolean isAlias = false;
        if (indexI.isConstant() && indexJ.isConstant() && indexI.getConstant() == indexJ.getConstant()) {
            isAlias = true;
        }
        if (indexI.isNAC() && (indexJ.isConstant() || indexJ.isNAC())) {
            isAlias = true;
        }
        if (indexJ.isNAC() && (indexI.isConstant() || indexI.isNAC())) {
            isAlias = true;
        }
        return isAlias;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact copy_in = in.copy();
        // check if stmt is DefinitionStmt
        if (stmt instanceof DefinitionStmt<?, ?>) {
            DefinitionStmt<LValue, RValue> defStmt = (DefinitionStmt<LValue, RValue>)stmt;
            LValue lValue = defStmt.getLValue();

            Value evaluated;
            RValue rValue = defStmt.getRValue();
            if (lValue instanceof Var && cp.canHoldInt((Var) lValue)) {
                if (rValue instanceof StaticFieldAccess || rValue instanceof InstanceFieldAccess || rValue instanceof ArrayAccess) {
                    evaluated = evaluate(rValue, copy_in);
                } else {
                    evaluated = cp.evaluate(rValue, copy_in);
                }
                copy_in.update((Var) lValue, evaluated);
            } else if (rValue instanceof Var && cp.canHoldInt((Var) rValue)) {
                if (lValue instanceof InstanceFieldAccess instanceFieldAccess) {
                    Var base = instanceFieldAccess.getBase();
                    JField jField = instanceFieldAccess.getFieldRef().resolve();
                    List<LoadField> loadFields = getStmtList(base, aliasLoadField);
                    for (LoadField loadField : loadFields) {
                        if (loadField.getFieldRef().resolve() == jField && !solver.getWorkList().contains(loadField)) {
                            solver.getWorkList().add(loadField);
                        }
                    }
                } else if (lValue instanceof StaticFieldAccess staticFieldAccess) {
                    for (Stmt st : icfg) {
                        if (st instanceof LoadField loadField
                         && loadField.isStatic()) {
                            JField jField = loadField.getFieldRef().resolve();
                            if (jField == staticFieldAccess.getFieldRef().resolve()) {
                                if (!solver.getWorkList().contains(loadField)) {
                                    solver.getWorkList().add(loadField);
                                }
                            }
                        }
                    }
                } else if (lValue instanceof ArrayAccess arrayAccess) {
                    Var base = arrayAccess.getBase();
                    List<LoadArray> loadArrays = getStmtList(base, aliasLoadArray);

                    for (LoadArray loadArray : loadArrays) {
                        if (!solver.getWorkList().contains(loadArray)) {
                            solver.getWorkList().add(loadArray);
                        }
                    }
                }
            }
        }
        CPFact copy_out = out.copy();
        out.clear();
        copy_in.forEach(out::update);
        return !copy_out.equals(out);
    }

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
// TODO 遇到 storeXxx时,就直接把所有别名的 LoadXxx加入 workList会死循环吗? 提交上去倒是不会,是因为 LoadXxx如果 CPFact没有发生改变就不会加入后继?