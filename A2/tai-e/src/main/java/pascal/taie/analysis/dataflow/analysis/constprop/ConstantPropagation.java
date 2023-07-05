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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        CPFact boundaryFact = newInitialFact();
        IR ir = cfg.getIR();
        ir.getParams().forEach(var -> {
            if (canHoldInt(var)) {
                boundaryFact.update(var, Value.getNAC());
            }
        });
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) -> {
            Value tarVal = target.get(var);
            Value newVal = meetValue(value, tarVal);
            target.update(var, newVal);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else if (v1.equals(v2)){
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            if (defStmt.getLValue() instanceof Var lValue) {
                boolean changed = false;
                for (Var inVar:in.keySet()) {
                    if (!inVar.equals(lValue)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                Exp exp = defStmt.getRValue();
                if (canHoldInt(lValue)) {
                    Value newVal = evaluate(exp, in);
                    return out.update(lValue, newVal) || changed;
                }
                else return changed;
            }
        }
        return out.copyFrom(in);
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
        if (exp instanceof IntLiteral val) {
            return Value.makeConstant(val.getValue());
        } else if (exp instanceof Var var) {
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        } else if (exp instanceof BinaryExp ex) {
            BinaryExp.Op op = ex.getOperator();
            Value val1 = evaluate(ex.getOperand1(), in);
            Value val2 = evaluate(ex.getOperand2(), in);

            if (op.equals(ArithmeticExp.Op.DIV) || op.equals(ArithmeticExp.Op.REM)) {
                if (val2.isConstant() && val2.getConstant() == 0) return Value.getUndef();
            }
            if (val1.isNAC() || val2.isNAC()) return Value.getNAC();

            if (val1.isConstant() && val2.isConstant()) {
                int i1 = val1.getConstant();
                int i2 = val2.getConstant();

                if (exp instanceof ArithmeticExp aExp) {
                    return switch (aExp.getOperator()) {
                        case ADD -> Value.makeConstant(i1 + i2);
                        case SUB -> Value.makeConstant(i1 - i2);
                        case MUL -> Value.makeConstant(i1 * i2);
                        case DIV -> Value.makeConstant(i1 / i2);
                        case REM -> Value.makeConstant(i1 % i2);
                    };
                } else if (exp instanceof BitwiseExp bExp) {
                    return switch (bExp.getOperator()) {
                        case OR -> Value.makeConstant(i1 | i2);
                        case AND -> Value.makeConstant(i1 & i2);
                        case XOR -> Value.makeConstant(i1 ^ i2);
                    };
                } else if (exp instanceof ConditionExp cExp) {
                    return switch (cExp.getOperator()) {
                        case EQ -> Value.makeConstant(i1 == i2 ? 1 : 0);
                        case NE -> Value.makeConstant(i1 != i2 ? 1 : 0);
                        case LT -> Value.makeConstant(i1 < i2 ? 1 : 0);
                        case GT -> Value.makeConstant(i1 > i2 ? 1 : 0);
                        case LE -> Value.makeConstant(i1 <= i2 ? 1 : 0);
                        case GE -> Value.makeConstant(i1 >= i2 ? 1 : 0);
                    };
                } else if (exp instanceof ShiftExp sExp) {
                    return switch (sExp.getOperator()) {
                        case SHL -> Value.makeConstant(i1 << i2);
                        case SHR -> Value.makeConstant(i1 >> i2);
                        case USHR -> Value.makeConstant(i1 >>> i2);
                    };
                }
            }

//            if (op.equals(ArithmeticExp.Op.MUL)) {
//                if ((val1.isNAC() && val2.isConstant() && val2.getConstant() == 0) ||
//                        (val2.isNAC() && val1.isConstant() && val1.getConstant() == 0))
//                    return Value.makeConstant(0);
//            }

            return Value.getUndef();
        } else return Value.getNAC();
    }
}
