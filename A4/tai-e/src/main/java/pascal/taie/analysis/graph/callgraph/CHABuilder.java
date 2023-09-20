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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.*;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                // callSitesIn: return the call sites within the given method.
                callGraph.callSitesIn(m).forEach(invoke -> {
                    // resolve: Resolves call targets (callees) of a call site via CHA.
                    Set<JMethod> T = resolve(invoke);
                    T.forEach(targetM -> {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, targetM));
                        workList.add(targetM);
                    });
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methodSet = new HashSet<>();
        InvokeExp invokeExp = callSite.getInvokeExp();
        MethodRef methodRef = invokeExp.getMethodRef();
        Subsignature m = methodRef.getSubsignature();
        // classTypeM: class type of m
        JClass classTypeM = methodRef.getDeclaringClass();
        // 框架是怎么知道每个Invoke的类型的?
        if (callSite.isStatic()) { // static methods
            JMethod staticMethod = classTypeM.getDeclaredMethod(m);
            assert staticMethod != null : "staticMethod != null fail";
            methodSet.add(staticMethod);
        } else if (callSite.isSpecial()) { // 1.constructors 2.private instance methods 3.superclass instance methods
            JMethod dispatched = dispatch(classTypeM, m);
            if (dispatched != null) {
                methodSet.add(dispatched);
            }
        } else if (callSite.isVirtual() || callSite.isInterface()) { // invoke interface, invoke virtual
            // TODO 怎么获取 receiver object
            // c = declared type of receiver variable at call site
            Var c = ((InvokeInstanceExp) invokeExp).getBase();
            JClass receiverClass = hierarchy.getClass(c.getType().getName());
            // foreach c' that is a subclass of c or c itself do: add Dispatch(c',m) to T
            // 因为 virtual调用时,receiverClass对象(c)可能指向它自己和它所有子类,所以要 getSubClasses
            getSubClasses(receiverClass).forEach(jClass -> {
                JMethod dispatched = dispatch(jClass, m);
                if (dispatched != null) {
                    methodSet.add(dispatched);
                }
            });
        }
        return methodSet;
    }

    private Set<JClass> getSubClasses(JClass jClass) {
        Set<JClass> classes = new HashSet<>();
        Queue<JClass> queue = new LinkedList<>();
        queue.add(jClass);
        while (!queue.isEmpty()) {
            JClass currentClass = queue.poll();
            if (currentClass.isInterface()) {
                queue.addAll(hierarchy.getDirectSubinterfacesOf(currentClass));
                queue.addAll(hierarchy.getDirectImplementorsOf(currentClass));
            } else {
                classes.add(currentClass);
                queue.addAll(hierarchy.getDirectSubclassesOf(currentClass));
            }
        }
        return classes;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     * 找不到就一直往父类找
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null) {
            return null;
        }
        JMethod method = jclass.getDeclaredMethod(subsignature);
        return (method != null && !method.isAbstract()) ? method : dispatch(jclass.getSuperClass(), subsignature);
    }
}
