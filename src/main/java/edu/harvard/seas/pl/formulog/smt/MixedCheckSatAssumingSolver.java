package edu.harvard.seas.pl.formulog.smt;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.util.Pair;

public class MixedCheckSatAssumingSolver extends AbstractSmtLibSolver {

    private final Map<SmtLibTerm, SolverVariable> indicatorVars = new HashMap<>();
    private int nextVarId;

    /*
    private void clearCache() throws EvaluationException {
        if (Configuration.timeSmt) {
            Configuration.recordCsaCacheClear(solverId);
        }
        indicatorVars.clear();
        nextVarId = 0;
        if (Configuration.smtCacheHardResets) {
            shim.reset();
            start();
        } else {
            shim.pop();
            shim.push();
        }
    }
    */

    public Set<SmtLibTerm> getCache() {
        return indicatorVars.keySet();
    }

    @Override
    protected Pair<Collection<SolverVariable>, Collection<SolverVariable>> makeAssertions(
            Collection<SmtLibTerm> formula) throws EvaluationException {
        int oldSize = indicatorVars.size();
        int hits = 0;
        int misses = 0;
        Set<SolverVariable> onVars = new HashSet<>();
        var it = formula.iterator();
        int size = oldSize;
        while (it.hasNext() && size < Configuration.smtCacheSize) {
            var conjunct = it.next();
            SolverVariable x = indicatorVars.get(conjunct);
            if (x != null) {
                hits++;
            } else {
                misses++;
                x = makeIndicatorVar(conjunct);
                indicatorVars.put(conjunct, x);
                SmtLibTerm imp = makeImp(x, conjunct);
                shim.makeAssertion(imp);
                size++;
            }
            onVars.add(x);
        }
        shim.push();
        while (it.hasNext()) {
            var conjunct = it.next();
            SolverVariable x = indicatorVars.get(conjunct);
            if (x == null) {
                misses++;
				shim.makeAssertion(conjunct);
            } else {
                hits++;
                onVars.add(x);
            }
        }
        if (Configuration.timeSmt) {
            Configuration.recordCsaCacheStats(solverId, hits, misses, oldSize);
        }
        Collection<SolverVariable> offVars;
        if (Configuration.smtUseNegativeLiterals) {
            offVars = indicatorVars.values().stream().filter(x -> !onVars.contains(x)).collect(Collectors.toList());
        } else {
            offVars = Collections.emptySet();
        }
        return new Pair<>(onVars, offVars);
    }

    private SmtLibTerm makeImp(SolverVariable x, SmtLibTerm assertion) {
        Term[] args = {x, assertion};
        return Constructors.make(BuiltInConstructorSymbol.SMT_IMP, args);
    }

    private SolverVariable makeIndicatorVar(SmtLibTerm assertion) {
        Term[] args = Terms.singletonArray(Terms.makeDummyTerm(nextVarId++));
        ParameterizedConstructorSymbol sym = GlobalSymbolManager
                .getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_VAR);
        sym = sym.copyWithNewArgs(Param.wildCard(), new Param(BuiltInTypes.bool, ParamKind.PRE_SMT_TYPE));
        return (SolverVariable) Constructors.make(sym, args);
    }

    @Override
    protected void cleanup() throws EvaluationException {
        shim.pop();
    }

    @Override
    protected void start() throws EvaluationException {
        shim.setLogic(Configuration.smtLogic);
        shim.makeDeclarations();
    }

    @Override
    protected boolean isIncremental() {
        return true;
    }

}
