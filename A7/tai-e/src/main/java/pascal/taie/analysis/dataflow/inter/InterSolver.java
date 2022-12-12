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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;

import java.util.LinkedList;
import java.util.Queue;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        var entries = icfg.entryMethods()
                .map(icfg::getEntryOf)
                .collect(Collectors.toSet());
        icfg.forEach(it -> {
            if (entries.contains(it)) {
                result.setInFact(it, analysis.newBoundaryFact(it));
                result.setOutFact(it, analysis.newBoundaryFact(it));
            } else {
                result.setInFact(it, analysis.newInitialFact());
                result.setOutFact(it, analysis.newInitialFact());
            }
        });
    }

    private void doSolve() {
        workList = new LinkedList<>(icfg.getNodes());
        while (!workList.isEmpty()) {
            var node = workList.poll();
            var in = result.getInFact(node);
            var out = result.getOutFact(node);
            icfg.getInEdgesOf(node)
                    .forEach(it -> {
                        var transferFact = analysis.transferEdge(it, result.getOutFact(it.getSource()));
                        analysis.meetInto(transferFact, in);
                    });
            if (analysis.transferNode(node, in, out)) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }

    public void addWorkList(Node node) {
        workList.add(node);
    }
}
