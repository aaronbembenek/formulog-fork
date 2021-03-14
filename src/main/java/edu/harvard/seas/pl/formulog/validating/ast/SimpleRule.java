package edu.harvard.seas.pl.formulog.validating.ast;

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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.AbstractRule;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralExnVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.FormulaRewriter;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ValidRule;

public class SimpleRule extends AbstractRule<SimplePredicate, SimpleLiteral> {

	public static SimpleRule make(ValidRule rule, FunctionCallFactory funcFactory) throws InvalidProgramException {
		Map<Var, Integer> varCounts = rule.countVariables();
		Simplifier simplifier = new Simplifier(varCounts);
		for (ComplexLiteral atom : rule) {
			try {
				simplifier.add(atom);
			} catch (InvalidProgramException e) {
				throw new InvalidProgramException("Problem simplifying this rule:\n" + rule
						+ "\nCould not simplify this atom: " + atom + "\nReason:\n" + e.getMessage());
			}
		}
		UserPredicate head = rule.getHead().applySubstitution(simplifier.getSubst());
		Set<Var> boundVars = simplifier.getBoundVars();
		if (!boundVars.containsAll(head.varSet())) {
			throw new InvalidProgramException("Unbound variables in head of rule:\n" + rule);
		}
		Term[] headArgs = head.getArgs();
		BindingType[] pat = computeBindingPattern(headArgs, boundVars, varCounts);
		SimplePredicate newHead = SimplePredicate.make(head.getSymbol(), head.getArgs(), pat, head.isNegated());
		FormulaRewriter fr = new FormulaRewriter(funcFactory);
		newHead = (SimplePredicate) rewriteFormulas(newHead, fr);
		List<SimpleLiteral> conjuncts = new ArrayList<>();
		for (SimpleLiteral lit : simplifier.getConjuncts()) {
			conjuncts.add(rewriteFormulas(lit, fr));
		}
		return new SimpleRule(newHead, conjuncts);
	}

	// XXX This isn't great because it doesn't check to make sure the invariants of
	// a SimpleRule are actually maintained.
//	public static SimpleRule make(SimplePredicate head, List<SimpleLiteral> body) {
//		return new SimpleRule(head, body);
//	}

	private SimpleRule(SimplePredicate head, List<SimpleLiteral> body) {
		super(head, body);
	}

	private static SimpleLiteral rewriteFormulas(SimpleLiteral lit, FormulaRewriter fr) {
		return lit.accept(new SimpleLiteralVisitor<Void, SimpleLiteral>() {

			@Override
			public SimpleLiteral visit(Assignment assignment, Void input) {
				Term newVal = fr.rewrite(assignment.getVal(), false);
				return Assignment.make(assignment.getDef(), newVal);
			}

			@Override
			public SimpleLiteral visit(Check check, Void input) {
				Term newLhs = fr.rewrite(check.getLhs(), false);
				Term newRhs = fr.rewrite(check.getRhs(), false);
				return Check.make(newLhs, newRhs, check.isNegated());
			}

			@Override
			public SimpleLiteral visit(Destructor destructor, Void input) {
				Term newScrutinee = fr.rewrite(destructor.getScrutinee(), false);
				ConstructorSymbol sym = destructor.getSymbol();
				Var[] bindings = destructor.getBindings();
				if (sym == BuiltInConstructorSymbol.ENTER_FORMULA || sym == BuiltInConstructorSymbol.EXIT_FORMULA) {
					assert bindings.length == 1;
					return Assignment.make(bindings[0], newScrutinee);
				}
				return Destructor.make(newScrutinee, sym, bindings);
			}

			@Override
			public SimpleLiteral visit(SimplePredicate pred, Void input) {
				Term[] args = pred.getArgs();
				Term[] newArgs = new Term[args.length];
				for (int i = 0; i < args.length; ++i) {
					newArgs[i] = fr.rewrite(args[i], false);
				}
				return SimplePredicate.make(pred.getSymbol(), newArgs, pred.getBindingPattern(), pred.isNegated());
			}
			
		}, null);
	}

	private static BindingType[] computeBindingPattern(Term[] args, Set<Var> boundVars, Map<Var, Integer> counts) {
		BindingType[] pat = new BindingType[args.length];
		for (int i = 0; i < pat.length; ++i) {
			Term arg = args[i];
			if (arg instanceof Var && Integer.valueOf(1).equals(counts.get(arg))) {
				pat[i] = BindingType.IGNORED;
			} else if (boundVars.containsAll(arg.varSet())) {
				pat[i] = BindingType.BOUND;
			} else {
				pat[i] = BindingType.FREE;
			}
		}
		return pat;
	}

	private static class Simplifier {

		private final List<SimpleLiteral> acc = new ArrayList<>();
		private final Set<Var> boundVars = new HashSet<>();
		private final Map<Var, Integer> varCounts;
		private final Substitution subst = new SimpleSubstitution();

		public Simplifier(Map<Var, Integer> varCounts) {
			this.varCounts = varCounts;
		}

		public Substitution getSubst() {
			return subst;
		}

		public void add(ComplexLiteral atom) throws InvalidProgramException {
			List<ComplexLiteral> todo = new ArrayList<>();
			atom = atom.applySubstitution(subst);
			SimpleLiteral c = atom.accept(new ComplexLiteralExnVisitor<Void, SimpleLiteral, InvalidProgramException>() {

				@Override
				public SimpleLiteral visit(UnificationPredicate unificationPredicate, Void input)
						throws InvalidProgramException {
					Term lhs = unificationPredicate.getLhs();
					Term rhs = unificationPredicate.getRhs();
					boolean leftBound = boundVars.containsAll(lhs.varSet());
					boolean rightBound = boundVars.containsAll(rhs.varSet());
					if (unificationPredicate.isNegated() && !(leftBound && rightBound)) {
						throw new InvalidProgramException();
					}
					if (leftBound && rightBound) {
						return Check.make(lhs, rhs, unificationPredicate.isNegated());
					} else if (rightBound) {
						if (lhs instanceof Var) {
							if (Configuration.inlineInRules || rhs instanceof Var) {
								subst.put((Var) lhs, rhs);
								return null;
							}
							return Assignment.make((Var) lhs, rhs);
						}
						if (!(lhs instanceof Constructor)) {
							throw new InvalidProgramException();
						}
						return makeDestructor(rhs, (Constructor) lhs, todo);
					} else if (leftBound) {
						if (rhs instanceof Var) {
							if (Configuration.inlineInRules || lhs instanceof Var) {
								subst.put((Var) rhs, lhs);
								return null;
							}
							return Assignment.make((Var) rhs, lhs);
						}
						if (!(rhs instanceof Constructor)) {
							throw new InvalidProgramException();
						}
						return makeDestructor(lhs, (Constructor) rhs, todo);
					} else {
						if (!(lhs instanceof Constructor) || !(rhs instanceof Constructor)) {
							throw new InvalidProgramException();
						}
						Constructor c1 = (Constructor) lhs;
						Constructor c2 = (Constructor) rhs;
						if (!c1.getSymbol().equals(c2.getSymbol())) {
							throw new InvalidProgramException("Unsatisfiable unification conjunct");
						}
						List<ComplexLiteral> cs = new ArrayList<>();
						Term[] args1 = c1.getArgs();
						Term[] args2 = c2.getArgs();
						for (int i = 0; i < args1.length; ++i) {
							cs.add(UnificationPredicate.make(args1[i], args2[i], false));
						}
						// XXX Not reordering because of type soundness issues.
						// ValidRule.order(cs, (p, xs) -> 1, new HashSet<>(boundVars), varCounts);
						for (ComplexLiteral c : cs) {
							todo.add(c);
						}
						return null;
					}
				}

				private Destructor makeDestructor(Term boundTerm, Constructor unboundCtor, List<ComplexLiteral> todo) {
					Term[] args = unboundCtor.getArgs();
					Var[] vars = new Var[args.length];
					for (int i = 0; i < args.length; ++i) {
						Var y = Var.fresh();
						vars[i] = y;
						todo.add(UnificationPredicate.make(y, args[i], false));
					}
					return Destructor.make(boundTerm, unboundCtor.getSymbol(), vars);
				}

				@Override
				public SimpleLiteral visit(UserPredicate userPredicate, Void input) {
					Term[] args = userPredicate.getArgs();
					Term[] newArgs = new Term[args.length];
					Set<Var> seen = new HashSet<>();
					for (int i = 0; i < args.length; ++i) {
						Term arg = args[i];
						if (boundVars.containsAll(arg.varSet())) {
							newArgs[i] = arg;
						} else if (arg instanceof Var && seen.add((Var) arg)) {
							newArgs[i] = arg;
						} else {
							Var y = Var.fresh();
							newArgs[i] = y;
							todo.add(UnificationPredicate.make(y, arg, false));
						}
					}
					BindingType[] pat = computeBindingPattern(newArgs, boundVars, varCounts);
					SimpleLiteral c = SimplePredicate.make(userPredicate.getSymbol(), newArgs, pat,
							userPredicate.isNegated());
					return c;
				}

			}, null);
			if (c != null) {
				acc.add(c);
				boundVars.addAll(c.varSet());
			}
			for (ComplexLiteral x : todo) {
				add(x);
			}
		}

		public List<SimpleLiteral> getConjuncts() {
			return acc;
		}

		public Set<Var> getBoundVars() {
			return boundVars;
		}

	}

}
