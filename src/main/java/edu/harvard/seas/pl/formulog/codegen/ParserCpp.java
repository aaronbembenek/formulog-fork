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

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Set;

public class ParserCpp extends TemplateSrcFile {

    public ParserCpp(CodeGenContext ctx) {
        super("parser.cpp", ctx);
    }

    public void gen(BufferedReader br, PrintWriter out) throws IOException {
        Worker w = new Worker(out);
        CodeGenUtil.copyOver(br, out, 0);
        w.defineParser();
        CodeGenUtil.copyOver(br, out, -1);
    }

    private class Worker {

        private final Set<ConstructorSymbol> symbols = ctx.getConstructorSymbols();
        private final PrintWriter out;

        public Worker(PrintWriter out) {
            this.out = out;
        }

        void defineParser() {
            for (ConstructorSymbol sym : symbols) {
                String symName = ctx.lookupRepr(sym);
                int arity = sym.getArity();
                String[] args = new String[arity];
                for (int i = 0; i < arity; i++)
                    args[i] = "terms[" + i + "]";
                out.printf("    case %s:\n", symName);
                out.printf("      return Term::make<%s>(%s);\n", symName, String.join(", ", args));
            }
        }

    }

}
