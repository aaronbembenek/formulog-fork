package edu.harvard.seas.pl.formulog.smt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;

public class HashMatchSmtSolver implements SmtLibSolver {

    private final SmtLibSolver[] solvers;
    private final Supplier<SmtLibSolver> solverFactory;
    private final double randProb;
    private final Map<Integer, Integer> directory = new HashMap<>();
    
    private final static AtomicInteger cacheHits = new AtomicInteger();
    
    public HashMatchSmtSolver(int size, Supplier<SmtLibSolver> solverFactory, double randProb) {
        solvers = new SmtLibSolver[size];
        this.solverFactory = solverFactory;
        this.randProb = randProb;
    }

    @Override
    public void start(Program<?, ?> prog) throws EvaluationException {
        for (int i = 0; i < solvers.length; ++i) {
            var solver = solverFactory.get();
            solver.start(prog);
            solvers[i] = solver;
        }
    }

    @Override
    public SmtResult check(Collection<SmtLibTerm> asserts, boolean getModel, int timeout) throws EvaluationException {
        var hashes = hashValues(asserts);
        int i;
        double flip = ThreadLocalRandom.current().nextDouble(1.0);
        int cell = 0;
        if (flip < randProb) {
            cell = ThreadLocalRandom.current().nextInt(solvers.length);
            i = 0;
        } else {
            i = hashes.size() - 1;
			for (; i >= 0; --i) {
			    Integer maybeCell = directory.get(hashes.get(i));
			    if (maybeCell != null) {
			        cell = maybeCell;
			        cacheHits.incrementAndGet();
			        break;
			    }
			}
			if (i < 0) {
			    cell = ThreadLocalRandom.current().nextInt(solvers.length);
			    i = 0;
			}
        }
        for (; i < hashes.size(); ++i) {
            directory.putIfAbsent(hashes.get(i), cell);
        }
        return solvers[cell].check(asserts, getModel, timeout);
    }
   
    private int choosePrefixLength(Collection<SmtLibTerm> asserts) {
        return asserts.size() - 1;
    }
    
    private List<Integer> hashValues(Collection<SmtLibTerm> asserts) {
        List<Integer> l = new ArrayList<>(asserts.size());
        // Based on boost::hash_combine
        int seed = 0;
        for (SmtLibTerm t : asserts) {
            seed ^= t.hashCode() + 0x9e3779b9 + (seed<<6) + (seed>>2);
            l.add(seed);
        }
        return l;
    }
   
    private int hash(Iterator<SmtLibTerm> it, int seed, int take) {
        // Based on boost::hash_combine
        for (int i = 0; i < take && it.hasNext(); ++i) {
            seed ^= it.next().hashCode() + 0x9e3779b9 + (seed<<6) + (seed>>2);
        }
        return seed;
    }

    @Override
    public void destroy() {
        for (var solver : solvers) {
            if (solver != null) {
                solver.destroy();
            }
        }
    }
    
    public static int getCacheHits() {
        return cacheHits.get();
    }

}
