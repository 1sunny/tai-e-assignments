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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>();
        cfg.forEach(B -> {
            if (!cfg.isEntry(B)) {
                workList.add(B);
            }
        });
        while (!workList.isEmpty()) {
            Node B = workList.poll();
            Fact INB = analysis.newInitialFact();
            result.setInFact(B, INB);
            cfg.getPredsOf(B).forEach(P -> analysis.meetInto(result.getOutFact(P), INB));
            boolean outChangeOccur = analysis.transferNode(B, result.getInFact(B), result.getOutFact(B));
            if (outChangeOccur) {
                cfg.getSuccsOf(B).forEach(S -> {
                    if (!workList.contains(S)) {
                        workList.add(S);
                    }
                });
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean change_occur = true;
        while (change_occur) {
            change_occur = false;
            for (Node B : cfg) {
                if (!cfg.isExit(B)) {
                    Fact OUTB = analysis.newInitialFact();
                    result.setOutFact(B, OUTB);
                    for (Node S : cfg.getSuccsOf(B)) {
                        analysis.meetInto(result.getInFact(S), OUTB);
                    }
                    change_occur |= analysis.transferNode(B, result.getInFact(B), OUTB);
                }
            }
        }
    }
}
