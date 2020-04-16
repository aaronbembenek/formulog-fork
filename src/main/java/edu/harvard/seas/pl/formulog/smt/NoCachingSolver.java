package edu.harvard.seas.pl.formulog.smt;

import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.util.Pair;

public class NoCachingSolver extends AbstractSmtLibSolver {

	private final static Pair<List<SolverVariable>, List<SolverVariable>> emptyListPair = new Pair<>(
			Collections.emptyList(), Collections.emptyList());

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> assertions) {
		shim.pop();
		shim.push();
		for (SmtLibTerm assertion : assertions) {
			shim.makeAssertion(assertion);
		}
		return emptyListPair;
	}

	@Override
	protected void cleanup() {
		// do nothing
	}

}
