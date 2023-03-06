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
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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
        // TODO - check
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj);
            workList.addEntry(
                    csManager.getCSVar(context,stmt.getLValue()),
                    PointsToSetFactory.make(csObj)
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context,stmt.getRValue()),
                    csManager.getCSVar(context,stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(
                        csManager.getCSVar(context,stmt.getRValue()),
                        csManager.getStaticField(field)
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(
                        csManager.getStaticField(field),
                        csManager.getCSVar(context,stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                Context context = contextSelector.selectContext(csManager.getCSCallSite(this.context, stmt), method);
                CSMethod csMethod = csManager.getCSMethod(context, method);

                callGraph.addEdge(
                        new Edge<>(CallGraphs.getCallKind(stmt),
                                csManager.getCSCallSite(this.context,stmt),
                                csMethod)
                );
                addReachable(csMethod);
                pass(csManager.getCSCallSite(this.context,stmt),csMethod);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - check
        if (pointerFlowGraph.addEdge(source,target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - check
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet delta = propagate(ptr, entry.pointsToSet());

            if (ptr instanceof CSVar varPtr) {
                Context context = varPtr.getContext();
                Var x = varPtr.getVar();

                for (CSObj obj : delta) {
                    // x.f = y
                    for (StoreField storeField : x.getStoreFields()) {
                        addPFGEdge(
                                csManager.getCSVar(context,storeField.getRValue()),
                                csManager.getInstanceField(obj,storeField.getFieldRef().resolve())
                        );
                    }
                    // y = x.f
                    for (LoadField loadField : x.getLoadFields()) {
                        addPFGEdge(
                                csManager.getInstanceField(obj,loadField.getFieldRef().resolve()),
                                csManager.getCSVar(context,loadField.getLValue())
                        );
                    }
                    // arr[*] = y
                    for (StoreArray storeArray : x.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(context,storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }
                    // y = arr[*]
                    for (LoadArray loadArray : x.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(context,loadArray.getLValue())
                        );
                    }
                    processCall(varPtr,obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - check
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet has = pointer.getPointsToSet();

        pointsToSet.objects().
                filter(ptr -> !has.contains(ptr)).
                forEach(ptr -> {has.addObject(ptr);delta.addObject(ptr);});

        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ,delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - check
        Context c = recv.getContext();
        Var var = recv.getVar();

        for (Invoke callSite : var.getInvokes()) {
            JMethod callee = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(c, callSite);

            Context ct = contextSelector.selectContext(csCallSite, recvObj, callee);
            workList.addEntry(csManager.getCSVar(ct,callee.getIR().getThis()),PointsToSetFactory.make(recvObj));

            CSMethod csCallee = csManager.getCSMethod(ct, callee);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite),csCallSite,csCallee))) {
                addReachable(csCallee);
                pass(csCallSite,csCallee);
            }
        }
    }

    private void pass(CSCallSite csCallSite, CSMethod csCallee) {
        Invoke callSite = csCallSite.getCallSite();
        JMethod callee = csCallee.getMethod();


        List<Var> args = callSite.getInvokeExp().getArgs();
        List<Var> params = csCallee.getMethod().getIR().getParams();

        Context c = csCallSite.getContext();
        Context ct = csCallee.getContext();

        for(int i = 0; i < args.size(); ++i){
            addPFGEdge(csManager.getCSVar(c, args.get(i)), csManager.getCSVar(ct, params.get(i)));
        }

        if(callSite.getLValue() != null){
            callee.getIR().getReturnVars().forEach(
                    ret -> {
                        addPFGEdge(
                                csManager.getCSVar(ct, ret),
                                csManager.getCSVar(c, callSite.getLValue()));
                    });
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
