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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Pair;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.meetValue;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.valMap;

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
        // TODO - check
        // WL
        workList = new LinkedList<>(icfg.getNodes());
        // CG
        for(Node node : icfg){
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private void doSolve() {
        // TODO - check
        while(!workList.isEmpty()){
            Node node = workList.poll();
            CPFact in = new CPFact();
            CPFact out = (CPFact) result.getOutFact(node);
            for(ICFGEdge<Node> edge : icfg.getInEdgesOf(node)){
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), (Fact) in);
            }
            handleStoreField((Stmt) node, in);
            handleStoreArray((Stmt) node, in);
            if(analysis.transferNode(node, (Fact) in, (Fact) out)){
                icfg.getSuccsOf(node).forEach(workList::offer);
            }
            result.setInFact(node, (Fact) in);
            result.setOutFact(node, (Fact) out);
        }
    }

    /**
     * 对数组的处理和对实例字段的处理类似。
     * 当分析一个数组的 load 语句如 x = a[i]; 时，
     * 你需要找到所有修改 a[i] 别名的值的 store 语句，并将这些值 meet 后赋给 x。
     * 此处对数组的处理要更复杂一些：当你判断两个对数组的访问 a[i] 和 b[j] 是否互为别名时，
     * 你不仅需要考虑它们的 base 变量（a 和 b）的指针集是否有交集，还需要考虑索引值 i 和 j 的关系。
     * 有趣的是，由于数组索引也是 int 类型，因此你可以用常量分析来实时计算 i 和 j 的关系。
     * @param stmt
     * @param in
     */
    private void handleStoreArray(Stmt stmt, CPFact in) {
        if(stmt instanceof StoreArray s){
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            ArrayAccess access = s.getArrayAccess();
            Value index = ConstantPropagation.evaluate(access.getIndex(), in);
            if(index.isUndef()) return; // UNDEF不互为别名
            Var base = access.getBase();
            pta.getPointsToSet(base).forEach(obj -> {
                Pair<Obj, Value> accessPair = new Pair<>(obj, index);
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                newVal = meetValue(oldVal, newVal);
                valMap.put(accessPair, newVal);
                if(!oldVal.equals(newVal)){
                    Set<Var> alias = aliasMap.get(obj);
                    alias.forEach(var -> {
                        var.getLoadArrays().forEach(loadStmt -> workList.offer((Node) loadStmt));
                    });
                }
            });
        }
    }


    /**
     * 当处理一个静态字段的 load 语句时（假设为 x = T.f;），你只需要找到对同一个字段（T.f）的 store 语句，
     * 并将这些保存进字段的值进行 meet 后赋给 load 语句等号左侧的变量（x）。
     * @param stmt
     * @param in
     */
    private void handleStoreField(Stmt stmt, CPFact in) {
        if(stmt instanceof StoreField s){
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            if(s.getFieldAccess() instanceof InstanceFieldAccess access) {
                Var base = access.getBase();
                pta.getPointsToSet(base).forEach(obj -> {
                    Pair<Obj, FieldRef> accessPair = new Pair<>(obj, s.getFieldRef());
                    Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                    Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                    newVal = meetValue(oldVal, newVal);
                    valMap.put(accessPair, newVal);
                    if(!oldVal.equals(newVal)){
                        Set<Var> alias = aliasMap.get(obj);
                        alias.forEach(var -> {
                            var.getLoadFields().stream()
                                    .filter(loadStmt -> loadStmt.getFieldAccess().getFieldRef().equals(s.getFieldRef()))
                                    .forEach(loadStmt -> workList.offer((Node) loadStmt));
                        });
                    }
                });
            }else if(s.getFieldAccess() instanceof StaticFieldAccess access){
                JClass clz = access.getFieldRef().getDeclaringClass();
                Pair<JClass, FieldRef> accessPair = new Pair<>(clz, s.getFieldRef());
                Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                newVal = meetValue(oldVal, newVal);
                valMap.put(accessPair, newVal);
                if (!oldVal.equals(newVal)) {
                    staticLoadFields.getOrDefault(accessPair, new HashSet<>()).forEach(loadStmt -> {
                        workList.offer((Node) loadStmt);
                    });
                }
            }
        }
    }
}
