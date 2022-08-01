package edu.harvard.seas.pl.formulog.codegen;

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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

public class MainCpp extends TemplateSrcFile {

    private final TermCodeGen tcg;

    public MainCpp(CodeGenContext ctx) {
        super("main.cpp", ctx);
        this.tcg = new TermCodeGen(ctx);
    }

    public void gen(BufferedReader br, PrintWriter out) throws IOException, CodeGenException {
        Worker pr = new Worker(out);
        CodeGenUtil.copyOver(br, out, 0);
        pr.loadExternalEdbs();
        CodeGenUtil.copyOver(br, out, 1);
        pr.loadExplicitFacts();
        /*
        CodeGenUtil.copyOver(br, out, 2);
        pr.printStratumFuncs();
        CodeGenUtil.copyOver(br, out, 3);
        pr.evaluate();
        CodeGenUtil.copyOver(br, out, 4);
        pr.printResults();
        */
        CodeGenUtil.copyOver(br, out, -1);
    }

    private class Worker {

        //    private final SortedIndexedFactDb db = ctx.getEval().getDb();
        private final PrintWriter out;

        public Worker(PrintWriter out) {
            this.out = out;
        }

        public void loadExternalEdbs() {
            for (RelationSymbol sym : ctx.getProgram().getFactSymbols()) {
                if (sym.isExternal()) {
                    loadExternalEdbs(sym);
                }
            }
        }

        public void loadExternalEdbs(RelationSymbol sym) {
            String func = "loadEdbs";
            CppExpr file = CppConst.mkString(sym + ".tsv");
            CppExpr repr = CppConst.mkString(ctx.lookupRepr(sym));
            CppExpr rel = CppMethodCall.mkThruPtr(CppVar.mk("globals::program"), "getRelation", repr);
            CppExpr call = CppFuncCall.mk(func, CppVar.mk("dir"), file, rel);
            call.toStmt().println(out, 1);
        }

        public void loadExplicitFacts() throws CodeGenException {
            var prog = ctx.getProgram();
            for (RelationSymbol sym : prog.getFactSymbols()) {
                for (Term[] tup : prog.getFacts(sym)) {
                    loadExplicitFact(sym, tup);
                }
            }
        }

        public void loadExplicitFact(RelationSymbol sym, Term[] tup) throws CodeGenException {
            List<CppExpr> args = new ArrayList<>();
            List<CppStmt> stmts = new ArrayList<>();
            TermCodeGen tcg = new TermCodeGen(ctx);
            for (Term t : tup) {
                try {
                    t = t.normalize(EmptySubstitution.INSTANCE);
                } catch (EvaluationException e) {
                    throw new CodeGenException("Could not normalize term occurring in fact: " + t);
                }
                Pair<CppStmt, CppExpr> p = tcg.gen(t, Collections.emptyMap());
                stmts.add(p.fst());
                args.add(p.snd());
            }
            CppExpr rel = CppConst.mkString(ctx.lookupRepr(sym));
            stmts.add(CppFuncCall.mk("loadFact", rel, CppVectorLiteral.mk(args)).toStmt());
            CppSeq.mk(stmts).println(out, 1);
        }

        /*
        public void loadEdbs() {
            for (RelationSymbol sym : db.getSymbols()) {
                if (sym.isEdbSymbol()) {
                    // XXX Should probably change this so that we explicitly
                    // load up only the master index, and then add the
                    // master index to all the other ones.
                    loadEdb(sym);
                }
            }
        }

        public void loadEdb(RelationSymbol sym) {
            Relation rel = ctx.lookupRelation(sym);
            for (Term[] tup : db.getAll(sym)) {
                Pair<CppStmt, List<CppExpr>> p = tcg.gen(Arrays.asList(tup), Collections.emptyMap());
                p.fst().println(out, 1);
                rel.mkInsert(rel.mkTuple(p.snd()), false).toStmt().println(out, 1);
            }
        }

        public void printStratumFuncs() {
            StratumCodeGen scg = new StratumCodeGen(ctx);
            List<Stratum> strata = ctx.getEval().getStrata();
            for (Iterator<Stratum> it = strata.iterator(); it.hasNext(); ) {
                printStratumFunc(it.next(), scg);
                if (it.hasNext()) {
                    out.println();
                }
            }
        }

        public void printStratumFunc(Stratum stratum, StratumCodeGen sgc) {
            out.println("void stratum_" + stratum.getRank() + "() {");
            sgc.gen(stratum).println(out, 1);
            out.println("}");
        }

        public void evaluate() {
            int n = ctx.getEval().getStrata().size();
            for (int i = 0; i < n; ++i) {
                CppFuncCall.mk("stratum_" + i, Collections.emptyList()).toStmt().println(out, 1);
            }
        }

     */

        public void printResults() {
            for (RelationSymbol sym : ctx.getProgram().getRuleSymbols()) {
                out.print("  cout << \"");
                out.print(sym);
                out.print(": \" << ");
                genRelationSize(sym).print(out);
                out.println(" << endl;");
                //CppIf.mk(CppVar.mk("dump"), ctx.lookupRelation(sym).mkPrint()).println(out, 1);
            }
        }

        private CppExpr genRelationSize(RelationSymbol sym) {
            String repr = ctx.lookupRepr(sym);
            CppExpr rel = CppMethodCall.mk(CppVar.mk("prog"), "getRelation", CppConst.mkString(repr));
            return CppMethodCall.mkThruPtr(rel, "size");
        }

    }

}
