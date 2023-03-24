package edu.harvard.seas.pl.formulog.eval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2023 President and Fellows of Harvard College
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

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.OverwriteSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public final class LocallyBatchedEagerStratumEvaluator extends AbstractStratumEvaluator {

	final int stratumNum;
	final SortedIndexedFactDb db;
	final CountingFJP exec;
	final Set<RelationSymbol> trackedRelations;
	Map<RelationSymbol, Set<Term[]>> deltaSets;

	static final int taskSize = Configuration.taskSize;
	static final int smtTaskSize = Configuration.smtTaskSize;
	static final int maxGen = Configuration.eagerEvalMaxGen;

	public LocallyBatchedEagerStratumEvaluator(int stratumNum, SortedIndexedFactDb db, Iterable<IndexedRule> rules,
			CountingFJP exec, Set<RelationSymbol> trackedRelations) {
		super(rules);
		this.stratumNum = stratumNum;
		this.db = db;
		this.exec = exec;
		this.trackedRelations = trackedRelations;
	}

	private Map<RelationSymbol, Set<Term[]>> resetDeltaSets() {
		var r = deltaSets;
		deltaSets = new HashMap<>();
		for (RelationSymbol sym : laterRoundRules.keySet()) {
			deltaSets.put(sym, Util.concurrentSet());
		}
		return r;
	}

	@Override
	public void evaluate() throws EvaluationException {
		resetDeltaSets();
		for (IndexedRule r : firstRoundRules) {
			exec.externallyAddTask(new RulePrefixEvaluator(r, null, 0));
		}
		exec.blockUntilFinished();
		if (exec.hasFailed()) {
			throw exec.getFailureCause();
		}
		while (true) {
			boolean didSomething = false;
			for (var e : resetDeltaSets().entrySet()) {
				var s = e.getValue();
				if (!s.isEmpty()) {
					for (var r : laterRoundRules.get(e.getKey())) {
						exec.externallyAddTask(new RulePrefixEvaluator(r, s, 0));
						didSomething = true;
					}
				}
			}
			exec.blockUntilFinished();
			if (exec.hasFailed()) {
				throw exec.getFailureCause();
			}
			if (!didSomething) {
				break;
			}
		}
	}

	Iterator<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s) throws EvaluationException {
		SimplePredicate predicate = (SimplePredicate) r.getBody(pos);
		int idx = r.getDbIndex(pos);
		Term[] args = predicate.getArgs();
		Term[] key = new Term[args.length];
		BindingType[] pat = predicate.getBindingPattern();
		for (int i = 0; i < args.length; ++i) {
			if (pat[i].isBound()) {
				key[i] = args[i].normalize(s);
			} else {
				key[i] = args[i];
			}
		}
		RelationSymbol sym = predicate.getSymbol();
		assert !(sym instanceof DeltaSymbol);
		Iterable<Term[]> ans = db.get(sym, key, idx);
		boolean shouldSplit = splitPositions.get(r)[pos];
		int targetSize = shouldSplit ? smtTaskSize : taskSize;
		return Util.splitIterable(ans, targetSize).iterator();
	}

	static final boolean recordRuleDiagnostics = Configuration.recordRuleDiagnostics;
	static final int batchSize = Configuration.eagerEvalBatchSize;

	@SuppressWarnings("serial")
	class RuleSuffixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final SimplePredicate head;
		final SimpleLiteral[] body;
		final int startPos;
		final OverwriteSubstitution s;
		final Iterator<Iterable<Term[]>> it;
		final boolean recursivePred;
		final List<Term[]> batch = new ArrayList<>(batchSize);
		final int gen;

		protected RuleSuffixEvaluator(IndexedRule rule, SimplePredicate head, SimpleLiteral[] body, int pos,
				OverwriteSubstitution s, Iterator<Iterable<Term[]>> it, int gen) {
			super(exec);
			this.rule = rule;
			this.head = head;
			this.body = body;
			this.startPos = pos;
			this.s = s;
			this.it = it;
			this.gen = gen;
			recursivePred = laterRoundRules.containsKey(head.getSymbol());
			if (Configuration.recordWork) {
				Configuration.workItems.incrementAndGet();
			}
		}

		protected RuleSuffixEvaluator(IndexedRule rule, int pos, OverwriteSubstitution s, Iterator<Iterable<Term[]>> it,
				int gen) {
			super(exec);
			this.rule = rule;
			this.head = rule.getHead();
			SimpleLiteral[] bd = new SimpleLiteral[rule.getBodySize()];
			for (int i = 0; i < bd.length; ++i) {
				bd[i] = rule.getBody(i);
			}
			this.body = bd;
			this.startPos = pos;
			this.s = s;
			this.it = it;
			this.gen = gen;
			recursivePred = laterRoundRules.containsKey(head.getSymbol());
			if (Configuration.recordWork) {
				Configuration.workItems.incrementAndGet();
			}
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, head, body, startPos, s.copy(), it, gen));
			}
			try {
				for (Term[] tup : tups) {
					evaluate(tup);
				}
			} catch (UncheckedEvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule: " + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRuleSuffixTime(rule, end - start);
			}
		}

		void evaluate(Term[] ans) throws UncheckedEvaluationException {
			SimplePredicate p = (SimplePredicate) body[startPos];
			updateBinding(p, ans);
			int pos = startPos + 1;
			@SuppressWarnings("unchecked")
			Iterator<Term[]>[] stack = new Iterator[rule.getBodySize()];
			boolean movingRight = true;
			while (pos > startPos) {
				if (pos == body.length) {
					try {
						reportFactBatched(head.getSymbol(), head.getArgs(), s);
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException(
								"Exception raised while evaluating the literal: " + head + "\n\n" + e.getMessage());
					}
					pos--;
					movingRight = false;
				} else if (movingRight) {
					SimpleLiteral l = body[pos];
					try {
						switch (l.getTag()) {
						case ASSIGNMENT:
							((Assignment) l).assign(s);
							pos++;
							break;
						case CHECK:
							if (((Check) l).check(s)) {
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case DESTRUCTOR:
							if (((Destructor) l).destruct(s)) {
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case PREDICATE:
							Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s);
							if (((SimplePredicate) l).isNegated()) {
								if (!tups.hasNext()) {
									pos++;
								} else {
									pos--;
									movingRight = false;
								}
							} else {
								if (tups.hasNext()) {
									stack[pos] = tups.next().iterator();
									if (tups.hasNext()) {
										exec.recursivelyAddTask(
												new RuleSuffixEvaluator(rule, head, body, pos, s.copy(), tups, gen));
									}
									// No need to do anything else: we'll hit the right case on the next iteration.
								} else {
									pos--;
								}
								movingRight = false;
							}
							break;
						}
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException(
								"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
					}
				} else {
					Iterator<Term[]> it = stack[pos];
					if (it != null && it.hasNext()) {
						ans = it.next();
						updateBinding((SimplePredicate) rule.getBody(pos), ans);
						movingRight = true;
						pos++;
					} else {
						stack[pos] = null;
						pos--;
					}
				}
			}
			dispatchBatch();
		}

		void updateBinding(SimplePredicate p, Term[] ans) {
			if (Configuration.recordWork) {
				Configuration.work.incrementAndGet();
			}
			Term[] args = p.getArgs();
			BindingType[] pat = p.getBindingPattern();
			for (int i = 0; i < pat.length; ++i) {
				if (pat[i].isFree()) {
					s.put((Var) args[i], ans[i]);
				}
			}
		}

		void reportFactBatched(RelationSymbol sym, Term[] args, Substitution s) throws EvaluationException {
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].normalize(s);
			}
			if (db.add(sym, newArgs)) {
				if (trackedRelations.contains(sym)) {
					System.err.println("[TRACKED] " + UserPredicate.make(sym, newArgs, false));
				}
				if (Configuration.recordWork) {
					Configuration.newDerivs.incrementAndGet();
				}
				if (recursivePred) {
					if (gen < maxGen) {
						batch.add(newArgs);
						if (batch.size() >= batchSize) {
							dispatchBatch();
						}
					} else {
						deltaSets.get(sym).add(newArgs);
					}
				}
			} else if (Configuration.recordWork) {
				Configuration.dupDerivs.incrementAndGet();
			}
		}

		void dispatchBatch() {
			if (!batch.isEmpty()) {
				var copy = new ArrayList<>(batch);
				batch.clear();
				Set<IndexedRule> rs = laterRoundRules.get(head.getSymbol());
				for (IndexedRule r : rs) {
					exec.recursivelyAddTask(new RulePrefixEvaluator(r, copy, gen + 1));
				}
			}
		}

	}

	@SuppressWarnings("serial")
	class RulePrefixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final Iterable<Term[]> deltaTups;
		final int gen;

		protected RulePrefixEvaluator(IndexedRule rule, Iterable<Term[]> deltaArgs, int gen) {
			super(exec);
			this.rule = rule;
			this.deltaTups = deltaArgs;
			this.gen = gen;
			if (Configuration.recordWork) {
				Configuration.workItems.incrementAndGet();
			}
		}

		void reportFact(RelationSymbol sym, Term[] args, Substitution s) throws EvaluationException {
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].normalize(s);
			}
			if (db.add(sym, newArgs)) {
				boolean recursivePred = laterRoundRules.containsKey(sym);
				if (recursivePred) {
					if (gen < maxGen) {
						for (IndexedRule r : laterRoundRules.get(sym)) {
							exec.recursivelyAddTask(
									new RulePrefixEvaluator(r, Collections.singletonList(newArgs), gen + 1));
						}
					} else {
						deltaSets.get(sym).add(newArgs);
					}
				}
				if (trackedRelations.contains(sym)) {
					System.err.println("[TRACKED] " + UserPredicate.make(sym, newArgs, false));
				}
				if (Configuration.recordWork) {
					Configuration.newDerivs.incrementAndGet();
				}
			} else if (Configuration.recordWork) {
				Configuration.dupDerivs.incrementAndGet();
			}
		}

		private Iterator<Iterable<Term[]>> handleDelta(int pos, Substitution s) throws EvaluationException {
			SimplePredicate pred = (SimplePredicate) rule.getBody(pos);
			List<Term[]> l = new ArrayList<>();
			BindingType[] bindings = pred.getBindingPattern();
			Term[] args = pred.getArgs();
			outer: for (var deltaTup : deltaTups) {
				if (Configuration.recordWork) {
					Configuration.work.incrementAndGet();
				}
				int i = 0;
				for (BindingType b : bindings) {
					Term arg = args[i];
					if (b.isBound() && !arg.normalize(s).equals(deltaTup[i])) {
						continue outer;
					}
					++i;
				}
				l.add(deltaTup);
			}
			boolean shouldSplit = splitPositions.get(rule)[pos];
			int targetSize = shouldSplit ? smtTaskSize : taskSize;
			return Util.splitIterable(l, targetSize).iterator();
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			try {
				evaluate();
			} catch (EvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule:\n" + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRulePrefixTime(rule, end - start);
			}
		}

		void evaluate() throws EvaluationException {
			int len = rule.getBodySize();
			int pos = 0;
			OverwriteSubstitution s = new OverwriteSubstitution();
			boolean foundDelta = false;
			loop: for (; pos < len; ++pos) {
				SimpleLiteral l = rule.getBody(pos);
				try {
					switch (l.getTag()) {
					case ASSIGNMENT:
						((Assignment) l).assign(s);
						break;
					case CHECK:
						if (!((Check) l).check(s)) {
							return;
						}
						break;
					case DESTRUCTOR:
						if (!((Destructor) l).destruct(s)) {
							return;
						}
						break;
					case PREDICATE:
						SimplePredicate p = (SimplePredicate) l;
						if (p.isNegated()) {
							if (lookup(rule, pos, s).hasNext()) {
								return;
							}
						} else {
							RelationSymbol sym = p.getSymbol();
							foundDelta = sym instanceof DeltaSymbol;
							break loop;
						}
						break;
					}
				} catch (EvaluationException e) {
					throw new EvaluationException(
							"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
				}
			}
			if (pos == len) {
				try {
					SimplePredicate head = rule.getHead();
					reportFact(head.getSymbol(), head.getArgs(), s);
					return;
				} catch (EvaluationException e) {
					throw new EvaluationException("Exception raised while evaluationg the literal: " + rule.getHead()
							+ e.getLocalizedMessage());
				}
			}
			Iterator<Iterable<Term[]>> tups;
			if (foundDelta) {
				tups = handleDelta(pos, s);
			} else {
				tups = lookup(rule, pos, s);
			}
			if (tups.hasNext()) {
				exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, pos, s, tups, gen));
			}
		}
	}

}
