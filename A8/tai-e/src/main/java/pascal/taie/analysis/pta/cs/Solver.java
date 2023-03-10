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
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.stmt.*;
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

    private TaintPointerFlowGraph taintPointerFlowGraph;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
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
        taintPointerFlowGraph = new TaintPointerFlowGraph();
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
        if (callGraph.contains(csMethod)) {
            return;
        }
        callGraph.addReachableMethod(csMethod);
        var stmtProcessor = new StmtProcessor(csMethod);
        for (var stmt : csMethod.getMethod().getIR()) {
            stmt.accept(stmtProcessor);
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

        @Override
        public Void visit(New stmt) {
            var xObj = heapModel.getObj(stmt);
            var heapContext = contextSelector.selectHeapContext(csMethod, xObj);

            var csVar = csManager.getCSVar(context, stmt.getLValue());
            var csObj = csManager.getCSObj(heapContext, xObj);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));

            return visitDefault(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            var source = csManager.getCSVar(context, stmt.getRValue());
            var target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);

            return visitDefault(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) {
                return visitDefault(stmt);
            }

            var source = csManager.getStaticField(stmt.getFieldRef().resolve());
            var target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);

            return visitDefault(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) {
                return visitDefault(stmt);
            }

            var source = csManager.getCSVar(context, stmt.getRValue());
            var target = csManager.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);

            return visitDefault(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return visitDefault(stmt);
            }

            var csCallSite = csManager.getCSCallSite(context, stmt);
            var callee = resolveCallee(null, stmt);
            var calleeContext = contextSelector.selectContext(csCallSite, callee);
            var csCallee = csManager.getCSMethod(calleeContext, callee);
            var result = stmt.getResult();

            var edge = new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csCallee);
            if (!callGraph.addEdge(edge)) {
                return visitDefault(stmt);
            }

            addReachable(csCallee);
            for (var i = 0; i < callee.getParamCount(); i++) {
                var param = callee.getIR().getParam(i);
                var arg = stmt.getInvokeExp().getArg(i);
                var source = csManager.getCSVar(context, arg);
                var target = csManager.getCSVar(calleeContext, param);
                addPFGEdge(source, target);
                if (result != null) {
                    var resultTarget = csManager.getCSVar(context, result);
                    taintAnalysis.getArg2ResultTypesOf(callee, i)
                            .forEach(it -> addTPFGEdge(source, resultTarget, it));
                }
            }

            if (result != null) {
                var target = csManager.getCSVar(context, result);
                for (var retVar : callee.getIR().getReturnVars()) {
                    var source = csManager.getCSVar(calleeContext, retVar);
                    addPFGEdge(source, target);
                }
                taintAnalysis.getSourceTypesOf(callee)
                        .stream()
                        .map(it -> taintAnalysis.getTaintObject(stmt, it))
                        .map(PointsToSetFactory::make)
                        .forEach(it -> workList.addEntry(target, it));
            }

            return visitDefault(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) {
            return;
        }
        var pts = source.getPointsToSet();
        if (!pts.isEmpty()) {
            workList.addEntry(target, pts);
        }
    }

    private void addTPFGEdge(Pointer source, Pointer target, Type type) {
        if (!taintPointerFlowGraph.addEdge(source, target, type)) {
            return;
        }
        var pts = PointsToSetFactory.make();
        source.getPointsToSet().objects()
                .map(CSObj::getObject)
                .filter(taintAnalysis::isTaint)
                .map(taintAnalysis::getSourceCall)
                .map(it -> taintAnalysis.getTaintObject(it, type))
                .forEach(pts::addObject);
        if (!pts.isEmpty()) {
            workList.addEntry(target, pts);
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {

        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var pointer = entry.pointer();
            var pts = entry.pointsToSet();
            var delta = propagate(pointer, pts);

            if (pointer instanceof CSVar csVar) {
                var variable = csVar.getVar();
                var context = csVar.getContext();
                for (var obj : delta) {
                    for (var stmt : variable.getLoadFields()) {
                        var field = stmt.getFieldRef().resolve();
                        var fieldPtr = csManager.getInstanceField(obj, field);
                        var target = csManager.getCSVar(context, stmt.getLValue());
                        addPFGEdge(fieldPtr, target);
                    }

                    for (var stmt : variable.getStoreFields()) {
                        var field = stmt.getFieldRef().resolve();
                        var fieldPtr = csManager.getInstanceField(obj, field);
                        var source = csManager.getCSVar(context, stmt.getRValue());
                        addPFGEdge(source, fieldPtr);
                    }

                    for (var stmt : variable.getLoadArrays()) {
                        var arr = csManager.getArrayIndex(obj);
                        var target = csManager.getCSVar(context, stmt.getLValue());
                        addPFGEdge(arr, target);
                    }

                    for (var stmt : variable.getStoreArrays()) {
                        var arr = csManager.getArrayIndex(obj);
                        var source = csManager.getCSVar(context, stmt.getRValue());
                        addPFGEdge(source, arr);
                    }

                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(target) and its PFG successors,
     * returns the difference set of pointsToSet and pt(target).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
        var oldPts = pointer.getPointsToSet();
        pointsToSet.objects()
                .filter(it -> !oldPts.contains(it))
                .forEach(delta::addObject);
        if (delta.isEmpty()) {
            return delta;
        }

        delta.forEach(csObj -> {
            oldPts.addObject(csObj);
            if (taintAnalysis.isTaint(csObj.getObject())) {
                var sourceCall = taintAnalysis.getSourceCall(csObj.getObject());
                taintPointerFlowGraph
                        .getEntriesOf(pointer)
                        .forEach(it -> {
                            var pts = PointsToSetFactory.make(taintAnalysis.getTaintObject(sourceCall, it.type()));
                            workList.addEntry(it.target(), pts);
                        });
            }
        });
        pointerFlowGraph.getSuccsOf(pointer)
                .forEach(it -> workList.addEntry(it, delta));
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        var context = recv.getContext();
        var var = recv.getVar();
        for (var stmt : var.getInvokes()) {
            var csCallSite = csManager.getCSCallSite(context, stmt);
            var callee = resolveCallee(recvObj, stmt);
            var calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            var csCallee = csManager.getCSMethod(calleeContext, callee);
            var result = stmt.getResult();

            var methodThis = csManager.getCSVar(calleeContext, callee.getIR().getThis());
            workList.addEntry(methodThis, PointsToSetFactory.make(recvObj));

            var edge = new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csCallee);
            if (!callGraph.addEdge(edge)) {
                continue;
            }

            addReachable(csCallee);
            for (var i = 0; i < callee.getParamCount(); i++) {
                var param = callee.getIR().getParam(i);
                var arg = stmt.getInvokeExp().getArg(i);
                var source = csManager.getCSVar(context, arg);
                var target = csManager.getCSVar(calleeContext, param);
                addPFGEdge(source, target);
                taintAnalysis.getArg2BaseTypesOf(callee, i)
                        .forEach(type -> addTPFGEdge(source, recv, type));
                if (result != null) {
                    var resultTarget = csManager.getCSVar(context, result);
                    taintAnalysis.getArg2ResultTypesOf(callee, i)
                            .forEach(it -> addTPFGEdge(source, resultTarget, it));
                }
            }

            if (result != null) {
                var target = csManager.getCSVar(context, result);
                for (var retVar : callee.getIR().getReturnVars()) {
                    var source = csManager.getCSVar(calleeContext, retVar);
                    addPFGEdge(source, target);
                }
                taintAnalysis.getSourceTypesOf(callee)
                        .stream()
                        .map(it -> taintAnalysis.getTaintObject(stmt, it))
                        .map(PointsToSetFactory::make)
                        .forEach(it -> workList.addEntry(target, it));
                taintAnalysis.getBase2ResultTypesOf(callee)
                        .forEach(it -> addTPFGEdge(recv, target, it));
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
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

class TaintPointerFlowGraph {
    private final Map<Pointer, Collection<TaintEntry>> taintPointerFlowGraph;

    record TaintEntry(Pointer target, Type type) {
    }

    TaintPointerFlowGraph() {
        taintPointerFlowGraph = new HashMap<>();
    }

    boolean addEdge(Pointer source, Pointer target, Type type) {
        return taintPointerFlowGraph
                .computeIfAbsent(source, it -> new HashSet<>())
                .add(new TaintEntry(target, type));
    }

    Collection<TaintEntry> getEntriesOf(Pointer source) {
        return taintPointerFlowGraph.getOrDefault(source, Collections.emptySet());
    }
}