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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - check
        // IN[exit] = 空
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - check
        // IN[B] = 空
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - check
        target.union(fact);
    }

    // transfer函数处理的是单条语句而非程序块!!!
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - check
        // 公式：IN[B] = use_B U (OUT[B]-def[B])
        // 对于Live Variables Analysis，因为是Backwards,所以out指的是IN[B],in指的是OUT[B],stmt指的是B

        // 保存旧的输出，也就是Old_IN[B]
        SetFact<Var> oldOut = out.copy();

        // IN[B] = OUT[B]
        out.union(in);

        // IN[B] = OUT[B]-def[B] - def
        stmt.getDef().ifPresent(def -> {
            if (def instanceof Var)
                out.remove((Var) def);
        });
        // use_B
        List<RValue> use_B = stmt.getUses();
        // + use
        // IN[B] = IN[B] U use_B
        use_B.forEach(use -> {
            if (use instanceof Var)
                out.add((Var) use);
        });
        // 与原来相比结果是否相同
        return !out.equals(oldOut);
    }
}
