package edu.harvard.seas.pl.formulog.smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
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
        int prefixLength = choosePrefixLength(asserts);
        var it = asserts.iterator();
        int key = hash(it, 0, prefixLength);
        Integer stored = directory.get(key);
        double flip = ThreadLocalRandom.current().nextDouble(1.0);
        int cell; 
        if (flip < randProb || stored == null) {
            cell = ThreadLocalRandom.current().nextInt(solvers.length);
        } else {
            cell = stored;
            cacheHits.incrementAndGet();
        }
        directory.put(hash(it, key, Integer.MAX_VALUE), cell);
        return solvers[cell].check(asserts, getModel, timeout);
    }
   
    private int choosePrefixLength(Collection<SmtLibTerm> asserts) {
        return asserts.size() - 1;
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
