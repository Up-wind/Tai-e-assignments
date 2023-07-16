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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

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
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.remove();
            callGraph.addReachableMethod(method);
            callGraph.callSitesIn(method).forEach(invoke -> {
                resolve(invoke).forEach(callee -> {
                    if (!callGraph.contains(callee)) {
                        workList.add(callee);
                    }
                    callGraph.addEdge(new Edge<>(
                            CallGraphs.getCallKind(invoke), invoke, callee));
                });
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> result = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass jClass = methodRef.getDeclaringClass();
        Subsignature subSig = methodRef.getSubsignature();
        if (callSite.isStatic() || callSite.isSpecial()) {
            result.add(dispatch(jClass, subSig));
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> workQueue = new ArrayDeque<>();
            workQueue.add(jClass);
            while (!workQueue.isEmpty()) {
                JClass jc = workQueue.remove();
                JMethod jm = dispatch(jc, subSig);
                if (jm != null) {
                    result.add(jm);
                }
                workQueue.addAll(hierarchy.getDirectSubclassesOf(jc));
                workQueue.addAll(hierarchy.getDirectSubinterfacesOf(jc));
                workQueue.addAll(hierarchy.getDirectImplementorsOf(jc));
            }
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod jm = jclass.getDeclaredMethod(subsignature);
        JClass superClass = jclass.getSuperClass();
        if ((jm != null && jm.isAbstract() && superClass != null) ||
                (jm == null && superClass != null)) {
            return dispatch(superClass, subsignature);
        }
        return jm;
    }
}
