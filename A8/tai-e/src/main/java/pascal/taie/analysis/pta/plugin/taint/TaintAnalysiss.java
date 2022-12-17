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
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Collectors;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

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

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        var result = solver.getResult();

        var csCallGraph = result.getCSCallGraph();
        var sinks = config.getSinks();
        csCallGraph.edges().forEach(it -> {
            var csCallSite = it.getCallSite();
            var csMethod = it.getCallee().getMethod();
            var context = csCallSite.getContext();
            var invoke = csCallSite.getCallSite();
            for (var i = 0; i < csMethod.getParamCount(); i++) {
                var arg = invoke.getInvokeExp().getArg(i);
                var sink = new Sink(csMethod, i);
                if (sinks.contains(sink)) {
                    csManager.getCSVar(context, arg)
                            .getPointsToSet()
                            .objects()
                            .map(CSObj::getObject)
                            .filter(manager::isTaint)
                            .map(obj -> new TaintFlow(manager.getSourceCall(obj), invoke, sink.index()))
                            .forEach(taintFlows::add);
                }
            }
        });

        return taintFlows;
    }

    public Collection<Type> getSourceTypesOf(JMethod method) {
        return config.getSources()
                .stream()
                .filter(it -> it.method() == method)
                .map(Source::type)
                .collect(Collectors.toSet());
    }

    private Collection<Type> getTransferTypesOf(JMethod method, int from, int to) {
        return config.getTransfers()
                .stream()
                .filter(it -> it.method().equals(method) && it.from() == from && it.to() == to)
                .map(TaintTransfer::type)
                .collect(Collectors.toSet());
    }

    public Collection<Type> getBase2ResultTypesOf(JMethod method) {
        return getTransferTypesOf(method, TaintTransfer.BASE, TaintTransfer.RESULT);
    }

    public Collection<Type> getArg2BaseTypesOf(JMethod method, int argIndex) {
        return getTransferTypesOf(method, argIndex, TaintTransfer.BASE);
    }

    public Collection<Type> getArg2ResultTypesOf(JMethod method, int argIndex) {
        return getTransferTypesOf(method, argIndex, TaintTransfer.RESULT);
    }

    public CSObj getTaintObject(Invoke source, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Invoke getSourceCall(Obj obj) {
        return manager.getSourceCall(obj);
    }
}
