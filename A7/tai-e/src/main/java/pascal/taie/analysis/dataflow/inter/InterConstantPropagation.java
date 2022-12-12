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
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final AliasTransferor transferor;

    private PointerAnalysisResult pta;

    // trace influenced loading vars to update work list.
    private final Map<FieldRef, Collection<LoadField>> staticLoadFieldTrace = new HashMap<>();

    private final Map<Var, Collection<LoadField>> instanceLoadFieldTrace = new HashMap<>();

    private final Map<Var, Collection<LoadArray>> loadArrayTrace = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        transferor = new AliasTransferor();
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // add tracing of loading vars
        pta.getVars().forEach(it -> {
            instanceLoadFieldTrace.put(it, new HashSet<>(it.getLoadFields()));
            loadArrayTrace.put(it, new HashSet<>(it.getLoadArrays()));
        });

        pta.getVars().forEach(var1 -> pta.getVars().forEach(var2 -> {
            if (var1 == var2) {
                return;
            }
            var pts1 = pta.getPointsToSet(var1);
            var pts2 = pta.getPointsToSet(var2);
            if (intersectsWith(pts1, pts2)) {
                instanceLoadFieldTrace.get(var1).addAll(var2.getLoadFields());
                loadArrayTrace.get(var1).addAll(var2.getLoadArrays());
            }
        }));

        // add tracing of static aliases
        pta.getCallGraph().reachableMethods().forEach(m -> m.getIR().forEach(stmt -> {
            if (stmt instanceof LoadField stLoadField && stLoadField.isStatic()) {
                var ref = stLoadField.getFieldRef();
                staticLoadFieldTrace
                        .computeIfAbsent(ref, k -> new HashSet<>())
                        .add(stLoadField);
            }
        }));
    }

    private static <T> boolean intersectsWith(Collection<T> set1, Collection<T> set2) {
        return set1.stream().anyMatch(set2::contains);
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
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof StoreField stStoreField) {
            return transferor.transferStoreField(stStoreField, in, out);
        }
        if (stmt instanceof LoadField stLoadField) {
            return transferor.transferLoadField(stLoadField, in, out);
        }
        if (stmt instanceof StoreArray stStoreArray) {
            return transferor.transferStoreArray(stStoreArray, in, out);
        }
        if (stmt instanceof LoadArray stLoadArray) {
            return transferor.transferLoadArray(stLoadArray, in, out);
        }
        return transferor.transferDefault(stmt, in, out);
    }

    protected class AliasTransferor {

        private final Map<ArrayAccess, Value> arrayMap = new HashMap<>();

        private final Map<Var, Value> arrayIndexMap = new HashMap<>();

        private final Map<FieldRef, Value> staticFieldMap = new HashMap<>();

        private final Map<InstanceFieldAccess, Value> instanceFieldMap = new HashMap<>();

        private boolean isAliasTo(InstanceFieldAccess field1, InstanceFieldAccess field2) {
            var pts1 = pta.getPointsToSet(field1.getBase());
            var pts2 = pta.getPointsToSet(field2.getBase());
            if (!intersectsWith(pts1, pts2)) {
                return false;
            }

            var ref1 = field1.getFieldRef().resolve();
            var ref2 = field2.getFieldRef().resolve();
            return ref1.equals(ref2);
        }

        private boolean isAliasTo(ArrayAccess array1, ArrayAccess array2, CPFact in) {
            var pts1 = pta.getPointsToSet(array1.getBase());
            var pts2 = pta.getPointsToSet(array2.getBase());
            if (!intersectsWith(pts1, pts2)) {
                return false;
            }

            var index1 = in.get(array1.getIndex());
            var index2 = in.get(array2.getIndex());

            if (index1.isUndef()) {
                index1 = arrayIndexMap.getOrDefault(array1.getIndex(), Value.getUndef());
            }
            return (index1.isConstant() && index2.isConstant() && index1.equals(index2)) ||
                    (index1.isConstant() && index2.isNAC()) ||
                    (index2.isConstant() && index1.isNAC());
        }

        public boolean transferStoreField(StoreField stmt, CPFact in, CPFact out) {
            var rv = stmt.getRValue();
            var rValue = in.get(rv);
            var field = stmt.getFieldAccess();

            if (field instanceof StaticFieldAccess staticField) {
                var value = staticFieldMap.getOrDefault(staticField.getFieldRef(), Value.getUndef());
                staticFieldMap.put(staticField.getFieldRef(), cp.meetValue(value, rValue));
            } else if (field instanceof InstanceFieldAccess instanceField) {
                var value = instanceFieldMap.getOrDefault(instanceField, Value.getUndef());
                instanceFieldMap.put(instanceField, cp.meetValue(value, rValue));
            }

            var flag = out.copyFrom(in);
            if (flag) {
                if (field instanceof StaticFieldAccess staticField) {
                    staticLoadFieldTrace
                            .getOrDefault(staticField.getFieldRef(), Collections.emptySet())
                            .stream()
                            .filter(s -> s.getFieldRef().resolve() == staticField.getFieldRef().resolve())
                            .findFirst()
                            .ifPresent(solver::addWorkList);

                } else if (field instanceof InstanceFieldAccess instanceField) {
                    instanceLoadFieldTrace
                            .getOrDefault(instanceField.getBase(), Collections.emptySet())
                            .stream()
                            .filter(s -> s.getFieldRef().resolve() == instanceField.getFieldRef().resolve())
                            .findFirst()
                            .ifPresent(solver::addWorkList);
                }
            }
            return flag;
        }

        public boolean transferStoreArray(StoreArray stmt, CPFact in, CPFact out) {
            var arrayAccess = stmt.getArrayAccess();
            var rv = stmt.getRValue();
            var index = arrayAccess.getIndex();
            var rValue = in.get(rv);
            if (!rValue.isUndef()) {
                var accessValue = arrayMap.getOrDefault(arrayAccess, Value.getUndef());
                arrayMap.put(arrayAccess, cp.meetValue(accessValue, rValue));
                var indexValue = in.get(index);
                if (indexValue.isConstant()) {
                    arrayIndexMap.put(index, indexValue);
                }
            }
            var flag = out.copyFrom(in);
            if (flag) {
                loadArrayTrace
                        .getOrDefault(arrayAccess.getBase(), Collections.emptySet())
                        .stream()
                        .findFirst()
                        .ifPresent(solver::addWorkList);
            }
            return flag;
        }

        public boolean transferLoadField(LoadField stmt, CPFact in, CPFact out) {
            var lv = stmt.getLValue();
            var ret = in.copy();
            var field = stmt.getFieldAccess();

            if (field instanceof StaticFieldAccess staticField) {
                var value = staticFieldMap.get(staticField.getFieldRef());
                if (value != null) {
                    ret.update(lv, value);
                }
            } else if (field instanceof InstanceFieldAccess instanceField) {
                var value = Value.getUndef();
                for (var entry : instanceFieldMap.entrySet()) {
                    var fieldAccess = entry.getKey();
                    if (isAliasTo(fieldAccess, instanceField)) {
                        value = cp.meetValue(value, entry.getValue());
                    }
                }
                if (!value.isUndef()) {
                    ret.update(lv, value);
                }
            }
            return out.copyFrom(ret);
        }

        public boolean transferLoadArray(LoadArray stmt, CPFact in, CPFact out) {
            var arrayAccess = stmt.getArrayAccess();
            var lv = stmt.getLValue();
            var ret = in.copy();
            var value = Value.getUndef();
            for (var entry : arrayMap.entrySet()) {
                var access = entry.getKey();
                if (isAliasTo(access, arrayAccess, in)) {
                    value = cp.meetValue(value, entry.getValue());
                }
            }
            if (!value.isUndef()) {
                ret.update(lv, value);
            }
            return out.copyFrom(ret);
        }

        public boolean transferDefault(Stmt stmt, CPFact in, CPFact out) {
            return cp.transferNode(stmt, in, out);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        var stmt = edge.getSource();
        var ret = out.copy();
        if (stmt instanceof Invoke invoke) {
            var result = invoke.getResult();
            if (result != null) {
                ret.remove(result);
            }
        }
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        var stmt = edge.getSource();
        var ret = newInitialFact();
        if (stmt instanceof Invoke invoke) {
            var args = invoke.getInvokeExp().getArgs();
            var params = edge.getCallee().getIR().getParams();
            assert args.size() == params.size();
            for (var i = 0; i < args.size(); i++) {
                var param = params.get(i);
                var arg = args.get(i);
                ret.update(param, callSiteOut.get(arg));
            }
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        var cs = edge.getCallSite();
        var ret = newInitialFact();

        var value = Value.getUndef();
        for (var retVar : edge.getReturnVars()) {
            value = cp.meetValue(value, returnOut.get(retVar));
        }

        if (cs instanceof Invoke stmt) {
            var result = stmt.getResult();
            if (result != null) {
                ret.update(result, value);
            }
        }
        return ret;
    }
}
