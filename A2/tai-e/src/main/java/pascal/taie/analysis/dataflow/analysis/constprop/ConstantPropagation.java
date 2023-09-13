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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import static pascal.taie.ir.exp.ArithmeticExp.Op.DIV;
import static pascal.taie.ir.exp.ArithmeticExp.Op.REM;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(var -> {
            // canHoldInt(Var) 方法来判断一个变量能否储存 int 类型的值。
            // 你需要利用这个方法来判断一个变量是否在本次作业的分析范围内，并忽略那些不在范围内的变量（例如 float 类型的变量）。
            if (canHoldInt(var)) {
                // 你要小心地处理每个会被分析的方法的参数。具体来说，你要将它们的值初始化为 NAC (请思考：为什么要这么做？)
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((kVar, vValue) -> {
            target.update(kVar, meetValue(vValue, target.get(kVar)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // at least one of them is nac
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        // at least one of them is undef
        if (v1.isUndef()) {
            return v2.isConstant() ? v2 : Value.getUndef();
        }
        if (v2.isUndef()) {
            return v1.isConstant() ? v1 : Value.getUndef();
        }
        // both v1 and v2 are const
        return v1.getConstant() == v2.getConstant() ? v1 : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact copy_in = in.copy();
        // check if stmt is DefinitionStmt
        if (stmt instanceof DefinitionStmt<?, ?>) {
            DefinitionStmt<LValue, RValue> defStmt = (DefinitionStmt<LValue, RValue>)stmt;
            // check LValue is Var:
            // 至于语句的处理，你只需要关注等号左侧为变量且右侧只能是如下几类表达式的赋值语句：
            // 常量，如 x = 1
            // 变量，如 x = y
            // 二元运算表达式，如 x = a + b 和 x = a >> b
            LValue lValue = defStmt.getLValue();
            if (lValue instanceof Var && canHoldInt((Var) lValue)) {
                Value evaluated = evaluate(defStmt.getRValue(), copy_in);
                copy_in.update((Var) lValue, evaluated);
            }
        }
        CPFact copy_out = out.copy();
        out.clear();
        copy_in.forEach((kVar, vValue) -> {
            out.update(kVar, vValue);
        });
        return !copy_out.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // v1, v2 应该都是 canHoldInt 吧,不然编译应该过不了
        // TODO - finish me
        if (exp instanceof IntLiteral exp1) {
            return Value.makeConstant(exp1.getValue());
        } else if (exp instanceof Var exp1) {
            assert canHoldInt(exp1): "canHoldInt(exp1) fail";
            return in.get(exp1);
        } else if (exp instanceof BinaryExp exp1) {
            Value v1 = in.get(exp1.getOperand1());
            Value v2 = in.get(exp1.getOperand2());
            // 也许因为除 0即使前面定义了这里可以为 Undef
            // if (v1.isUndef() || v2.isUndef()) {
            //    System.err.println("exp: " + exp);
            //    assert false: "isUndef here";
            // }
            if (v2.isConstant() && v2.getConstant() == 0
                    && exp1.getOperator() instanceof ArithmeticExp.Op op1
                    && (op1 == DIV || op1 == REM)) {
                return Value.getUndef();
            }
            if (v1.isConstant() && v2.isConstant()) {
                int c1 = v1.getConstant();
                int c2 = v2.getConstant();
                BinaryExp.Op op = exp1.getOperator();
                Value result = null;
                if (op instanceof ArithmeticExp.Op op1) {
                    result = switch (op1) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> Value.makeConstant(c1 / c2);
                        case REM -> Value.makeConstant(c1 % c2);
                    };
                } else if (op instanceof ConditionExp.Op op1) {
                    result = switch (op1) {
                        case EQ -> Value.makeConstant(c1 == c2 ? 1 : 0);
                        case NE -> Value.makeConstant(c1 != c2 ? 1 : 0);
                        case LT -> Value.makeConstant(c1 < c2 ? 1 : 0);
                        case GT -> Value.makeConstant(c1 > c2 ? 1 : 0);
                        case LE -> Value.makeConstant(c1 <= c2 ? 1 : 0);
                        case GE -> Value.makeConstant(c1 >= c2 ? 1 : 0);
                    };
                } else if (op instanceof ShiftExp.Op op1) {
                    result = switch (op1) {
                        case SHL -> Value.makeConstant(c1 << c2);
                        case SHR -> Value.makeConstant(c1 >> c2);
                        case USHR -> Value.makeConstant(c1 >>> c2);
                    };
                } else if (op instanceof BitwiseExp.Op op1) {
                    result = switch (op1) {
                        case OR -> Value.makeConstant(c1 | c2);
                        case AND -> Value.makeConstant(c1 & c2);
                        case XOR -> Value.makeConstant(c1 ^ c2);
                    };
                }
                assert result != null : "result != null fail";
                return result;
            } else if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}

/*
undef:
比如第一个BB里面定义了x,那么处理第二个BB的I|N时,x在meetInto.meetValue里面就是UNDEF,x的值就取决于第一个BB里的值

definition是赋值?

易错:
1.params canHoldInt 否则会多 NAC导致不同, defStmt 判断canHoldInt
2.nac / 0
 */