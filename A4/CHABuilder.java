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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

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
        // TODO - check
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while(!workList.isEmpty()){
            JMethod m = workList.poll();

            if(callGraph.contains(m)){
                continue;
            }
            // add m to RM
            callGraph.addReachableMethod(m);
            // foreach call site cs in m do
            for(Stmt stmt : m.getIR().getStmts()){
                if(stmt instanceof Invoke cs){
                    // T = Resolve(cs)
                    // foreach target method m1 in T do
                    for(JMethod m1 : resolve(cs)){
                        // add cs->m1 to CG
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, m1));
                        // add m1 to WL
                        workList.add(m1);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - check
        // T={}
        Set<JMethod> T = new HashSet<>();
        // m = method signature at cs
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        JClass declaringClass = methodRef.getDeclaringClass();
        JMethod m = declaringClass.getDeclaredMethod(subsignature);
        // if cs is static call Then
        //      T = {m}
        if (callSite.isStatic()) {
            T.add(m);
        }
        // if cs is special call Then
        //      Cm = class type of m
        //      T = {Dispatch(Cm,m)}
        if (callSite.isSpecial()) {
            T.add(dispatch(declaringClass, subsignature));
        }
        // if cs is a virtual call or interface Then
        if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> queue = new LinkedList<>();
            queue.add(declaringClass);

            while (!queue.isEmpty()) {
                JClass cur = queue.poll();
                JMethod dispatchMethod = dispatch(cur, subsignature);
                if (dispatchMethod != null) {
                    T.add(dispatchMethod);
                }
                if (cur.isInterface()) {
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(cur));
                    queue.addAll(hierarchy.getDirectImplementorsOf(cur));
                } else {
                    queue.addAll(hierarchy.getDirectSubclassesOf(cur));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass c, Subsignature subsignature) {
        // TODO - check
        if (c == null) {
            return null;
        }

        JMethod m = c.getDeclaredMethod(subsignature);
        if (m != null && !m.isAbstract()) {
            return m;
        }
        return dispatch(c.getSuperClass(), subsignature);
    }
}
