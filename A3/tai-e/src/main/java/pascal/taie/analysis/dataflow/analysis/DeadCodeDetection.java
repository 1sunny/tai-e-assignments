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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Map<Stmt, Boolean> active = new HashMap<Stmt, Boolean>();
        Map<Stmt, Boolean> visit = new HashMap<Stmt, Boolean>();

        active.put(cfg.getExit(), true);

        traverseCfg(cfg, cfg.getEntry(), visit, active, constants, liveVars);

        cfg.forEach(stmt -> {
            if (!active.containsKey(stmt)) {
                deadCode.add(stmt);
            }
        });
        return deadCode;
    }

    private void traverseCfg(CFG<Stmt> cfg, Stmt stmt, Map<Stmt, Boolean> visit, Map<Stmt, Boolean> active, DataflowResult<Stmt, CPFact> constants, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        /**
         *       DefinitionStmt
         *       /         \
         *   Invoke      AssignStmt
         * e.g. x=f()     /       \
         *        AssignLiteral   Copy
         *        e.g. x = 1      e.g. x = y
         */
        if (visit.containsKey(stmt)) {
            return;
        }
        visit.put(stmt, true);
        // check if stmt is a assignStmt statement
        if (stmt instanceof AssignStmt<?,?>) {
            AssignStmt<LValue, RValue> defStmt = (AssignStmt<LValue, RValue>) stmt;

            LValue lValue = defStmt.getLValue();
            // check left side is variable & right side has no effect(e.g. may raise exception)
            if (lValue instanceof Var && hasNoSideEffect(defStmt.getRValue())) {
                // check left side is a live variable
                if (liveVars.getOutFact(stmt).contains((Var) lValue)) {
                    active.put(stmt, true);
                }
            } else {
                active.put(stmt, true);
            }
        } else {
            // not a assignStmt statement, it's active
            active.put(stmt, true);
        }
        if (stmt instanceof If ifStmt) {
            // check op1 & op2 are constant
            Value v1 = constants.getInFact(stmt).get(ifStmt.getCondition().getOperand1());
            Value v2 = constants.getInFact(stmt).get(ifStmt.getCondition().getOperand2());
            final boolean goTrue; // lambda requires to be final or efficient final
            final boolean goFalse;
            if (v1.isConstant() && v2.isConstant()) {
                if (isIfConditionTrue(ifStmt, v1, v2)) {
                    goFalse = false;
                    goTrue = true;
                } else {
                    goTrue = false;
                    goFalse = true;
                }
            } else {
                // can't decide the value of condition statement, both edge should go
                goTrue = true;
                goFalse = true;
            }
            cfg.getOutEdgesOf(stmt).forEach(stmtEdge -> {
                if (stmtEdge.getKind() == Edge.Kind.IF_TRUE && goTrue
                 || stmtEdge.getKind() == Edge.Kind.IF_FALSE && goFalse) {
                    traverseCfg(cfg, stmtEdge.getTarget(), visit, active, constants, liveVars);
                }
            });
        } else if (stmt instanceof SwitchStmt switchStmt) {
            Value value = constants.getInFact(stmt).get(switchStmt.getVar());
            if (value.isConstant()) {
                boolean findCase = false;
                Iterator<Pair<Integer, Stmt>> caseIterator = switchStmt.getCaseTargets().iterator();
                // try to find a match branch
                while (caseIterator.hasNext()) {
                    Pair<Integer, Stmt> casePair = caseIterator.next();
                    if (casePair.first() == value.getConstant()) {
                        findCase = true;
                        traverseCfg(cfg, casePair.second(), visit, active, constants, liveVars);
                        break;
                    }
                }
                if (!findCase) {
                    // traverse default branch
                    traverseCfg(cfg, switchStmt.getDefaultTarget(), visit, active, constants, liveVars);
                }
            } else {
                // switch x, x is not a constant, traverse all out edges
                cfg.getOutEdgesOf(stmt).forEach(stmtEdge -> traverseCfg(cfg, stmtEdge.getTarget(), visit, active, constants, liveVars));
            }
        } else {
            // not if, not switch, traverse all out edges
            cfg.getOutEdgesOf(stmt).forEach(stmtEdge -> traverseCfg(cfg, stmtEdge.getTarget(), visit, active, constants, liveVars));
        }
    }

    /**
     *
     * @param ifStmt
     * @param v1
     * @param v2
     * @return true if the If statement's condition is true
     */
    private static boolean isIfConditionTrue(If ifStmt, Value v1, Value v2) {
        boolean conditionIsTrue;
        switch (ifStmt.getCondition().getOperator()) {
            case EQ -> conditionIsTrue = (v1.getConstant() == v2.getConstant());
            case NE -> conditionIsTrue = (v1.getConstant() != v2.getConstant());
            case LT -> conditionIsTrue = (v1.getConstant() < v2.getConstant());
            case GT -> conditionIsTrue = (v1.getConstant() > v2.getConstant());
            case LE -> conditionIsTrue = (v1.getConstant() <= v2.getConstant());
            case GE -> conditionIsTrue = (v1.getConstant() >= v2.getConstant());
            default -> throw new RuntimeException("operator no match");
        }
        return conditionIsTrue;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
