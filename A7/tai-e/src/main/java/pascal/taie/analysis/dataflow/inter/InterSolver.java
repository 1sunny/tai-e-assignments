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
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
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

    DataflowResult<Node, Fact> getResult() {
        return result;
    }

    Queue<Node> getWorkList(){
        return workList;
    }

    private void initialize() {
        // TODO - finish me
        workList = new LinkedList<>();
        // 在初始化的过程中，过程间求解器需要初始化程序中所有的 IN/OUT fact，也就是 ICFG 的全部节点。
        // 但你仅需要对 ICFG 的 entry 方法（比如 main 方法）的 entry 节点设置 boundary fact。
        // 这意味着其他方法的 entry 节点和非 entry 节点的初始 fact 是一样的。
        icfg.entryMethods().forEach(entryM -> {
            Node entry = icfg.getEntryOf(entryM);
            result.setInFact(entry, analysis.newBoundaryFact(entry));
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
        for (Node node : icfg) {
            boolean entryNode = icfg.entryMethods().allMatch(method -> icfg.getEntryOf(method) == node);
            if (!entryNode) {
                workList.add(node);
                // 在初始化的过程中，过程间求解器需要初始化程序中所有的 IN/OUT fact，也就是 ICFG 的全部节点。
                // 但你仅需要对 ICFG 的 entry 方法（比如 main 方法）的 entry 节点设置 boundary fact。
                // 这意味着其他方法的 entry 节点和非 entry 节点的初始 fact 是一样的。
                result.setInFact(node, analysis.newInitialFact()); // ugly
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            Node B = workList.poll();
            // 在计算一个节点的 IN fact 时，过程间求解器需要对传入的 edge 和前驱们的 OUT facts 应用 edge transfer 函数（transferEdge）
            icfg.getInEdgesOf(B).forEach(edge -> {
                Fact outP = result.getOutFact(edge.getSource());
                analysis.meetInto(analysis.transferEdge(edge, outP), result.getInFact(B));
            });
            boolean outChangeOccur = analysis.transferNode(B, result.getInFact(B), result.getOutFact(B));
            if (outChangeOccur) {
                icfg.getSuccsOf(B).forEach(S -> {
                    if (!workList.contains(S)) {
                        workList.add(S);
                    }
                });
            }
        }
    }
}

// TODO 分析 x = this.f 时, this.f 还不是常量, 但在后面的处理中被赋为常量了, 这种情况怎么办
// Run 不会展示NAC, Debug运行会?