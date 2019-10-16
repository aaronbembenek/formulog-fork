package edu.harvard.seas.pl.formulog.parsing;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import static edu.harvard.seas.pl.formulog.util.Util.map;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogLexer;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AdtDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AggTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AggTypeListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AnnotationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AtomListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.BinopFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.BinopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ClauseStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ConsTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ConstSymFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ConstructorTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.DisunificationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.DoubleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FactStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FloatTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FormulaTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FunDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.HoleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.I32TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.I64TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IfExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IndexContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IndexedFunctorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IteTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.LetExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.LetFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ListTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.MatchClauseContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.MatchExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NegatedAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NonEmptyTermListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NormalAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NotFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.OutermostCtorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ParensTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.PredicateContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.QuantifiedFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.QueryStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordEntryContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordEntryDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordUpdateTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RelDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.SmtEqTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.SpecialFPTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.StringTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermSymFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TupleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TupleTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeAliasContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDefRHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeRefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeVarContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UnificationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UninterpFunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UninterpSortDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UnopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.VarTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.IndexedConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.IndexedTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.MutableRelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.RecordSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbolType;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeAlias;
import edu.harvard.seas.pl.formulog.types.TypeManager;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class Parser {

	private final SymbolManager symbolManager = new SymbolManager();
	private final TypeManager typeManager = new TypeManager();

	public Parser() {
		symbolManager.initialize();
	}

	private FormulogParser getParser(Reader r) throws ParseException {
		try {
			CharStream chars = CharStreams.fromReader(r);
			FormulogLexer lexer = new FormulogLexer(chars);
			CommonTokenStream tokens = new CommonTokenStream(lexer);
			return new FormulogParser(tokens);
		} catch (IOException e) {
			throw new ParseException(e.getMessage());
		}
	}

	public BasicProgram parse(Reader r) throws ParseException {
		return parse(r, Paths.get(""));
	}

	public BasicProgram parse(Reader r, Path inputDir) throws ParseException {
		try {
			FormulogParser parser = getParser(r);
			StmtProcessor stmtProcessor = new StmtProcessor(inputDir);
			parser.prog().accept(stmtProcessor);
			return stmtProcessor.getProgram();
		} catch (Exception e) {
			throw new ParseException(e.getMessage());
		}
	}

	private static List<Integer> getIndices(IndexContext ctx) {
		return map(ctx.INT(), d -> Integer.parseInt(d.getText()));
	}

	private final FormulogVisitor<Type> typeExtractor = new FormulogBaseVisitor<Type>() {

		@Override
		public Type visitTupleType(TupleTypeContext ctx) {
			List<Type> typeArgs = map(ctx.type(), t -> t.accept(this));
			TypeSymbol sym = symbolManager.lookupTupleTypeSymbol(typeArgs.size());
			return AlgebraicDataType.make(sym, typeArgs);
		}

		@Override
		public Type visitTypeVar(TypeVarContext ctx) {
			return TypeVar.get(ctx.getText());
		}

		@Override
		public Type visitTypeRef(TypeRefContext ctx) {
			List<Type> params = map(ctx.type(), t -> t.accept(this));
			String s = ctx.ID().getText();
			List<Integer> indices = getIndices(ctx.index());
			switch (s) {
			case "i32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i32 does not have any type parameters.");
				}
				return BuiltInTypes.i32;
			case "i64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i64 does not have any type parameters.");
				}
				return BuiltInTypes.i64;
			case "fp32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp32 does not have any type parameters.");
				}
				return BuiltInTypes.fp32;
			case "fp64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp64 does not have any type parameters.");
				}
				return BuiltInTypes.fp64;
			case "string":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type string does not have any type parameters.");
				}
				return BuiltInTypes.string;
			default:
				String name = ctx.ID().getText();
				TypeSymbol sym;
				if (!indices.isEmpty()) {
					Pair<IndexedTypeSymbol, List<Integer>> p = symbolManager.lookupIndexedTypeSymbol(name, indices);
					sym = p.fst();
					indices = p.snd();
					params.addAll(map(indices, i -> TypeIndex.make(i)));
				} else {
					Symbol sym2 = symbolManager.lookupSymbol(name);
					if (!(sym2 instanceof TypeSymbol)) {
						throw new RuntimeException("Not a type symbol: " + sym2);
					}
					sym = (TypeSymbol) sym2;
				}
				return typeManager.lookup(sym, params);
			}
		}

	};

	private final class StmtProcessor extends FormulogBaseVisitor<Void> {

		private final Map<RelationSymbol, Set<Term[]>> initialFacts = new HashMap<>();
		private final Map<RelationSymbol, Set<BasicRule>> rules = new HashMap<>();
		private final FunctionDefManager functionDefManager = new FunctionDefManager();
		private final FunctionCallFactory functionCallFactory = new FunctionCallFactory(functionDefManager);
		private final Map<FunctionSymbol, Pair<AlgebraicDataType, Integer>> recordLabels = new HashMap<>();
		private final Map<ConstructorSymbol, FunctionSymbol[]> constructorLabels = new HashMap<>();
		private final Set<RelationSymbol> externalEdbs = new HashSet<>();
		private final VariableCheckPass varChecker = new VariableCheckPass(symbolManager);
		private final Set<ConstructorSymbol> uninterpFuncSymbols = new HashSet<>();
		private final Path inputDir;
		private UserPredicate query;

		public StmtProcessor(Path inputDir) {
			this.inputDir = inputDir;
		}

		@Override
		public Void visitFunDecl(FunDeclContext ctx) {
			List<Pair<FunctionSymbol, List<Var>>> ps = map(ctx.funDefLHS(), this::parseFunDefLHS);
			Iterator<Term> bodies = map(ctx.term(), e -> e.accept(termExtractor)).iterator();
			for (Pair<FunctionSymbol, List<Var>> p : ps) {
				FunctionSymbol sym = p.fst();
				List<Var> args = p.snd();
				Term body = bodies.next();
				try {
					Term newBody = varChecker.checkFunction(args, body);
					functionDefManager.register(UserFunctionDef.get(sym, args.toArray(new Var[0]), newBody));
				} catch (ParseException e) {
					throw new RuntimeException(
							"Error in definition for function " + sym + ": " + e.getMessage() + "\n" + body);
				}
			}
			return null;
		}

		private Pair<FunctionSymbol, List<Var>> parseFunDefLHS(FunDefLHSContext ctx) {
			String name = ctx.ID().getText();
			List<Type> argTypes = map(ctx.args.type(), t -> t.accept(typeExtractor));
			Type retType = ctx.retType.accept(typeExtractor);
			FunctionSymbol sym = symbolManager.createFunctionSymbol(name, argTypes.size(),
					new FunctorType(argTypes, retType));
			List<Var> args = map(ctx.args.VAR(), x -> Var.make(x.getText()));
			if (args.size() != new HashSet<>(args).size()) {
				throw new RuntimeException(
						"Cannot use the same variable multiple times in a function declaration: " + name);
			}
			return new Pair<>(sym, args);
		}

		List<Type> getRelationTypes(AggTypeListContext ctx) {
			List<Type> types = new ArrayList<>();
			for (Iterator<AggTypeContext> it = ctx.aggType().iterator(); it.hasNext();) {
				AggTypeContext agctx = it.next();
				types.add(agctx.type().accept(typeExtractor));
			}
			return types;
		}

		void setAggregate(RelationSymbol rel, AggTypeListContext ctx) {
			// for (Iterator<AggTypeContext> it = ctx.aggType().iterator(); it.hasNext();) {
			// AggTypeContext agctx = it.next();
			// if (agctx.func != null) {
			// if (it.hasNext()) {
			// throw new RuntimeException(
			// "Aggregates can only be set for the last column of a relation: " + rel);
			// }
			// Symbol funcSym = symbolManager.lookupSymbol(agctx.func.getText());
			// if (!(funcSym instanceof FunctionSymbol)) {
			// throw new RuntimeException("Non-function used in aggregate: " + funcSym);
			// }
			// Term unit = extract(agctx.unit);
			// rel.setAggregate((FunctionSymbol) funcSym, unit);
			// }
			// }
		}

		@Override
		public Void visitRelDecl(RelDeclContext ctx) {
			String name = ctx.ID().getText();
			List<Type> types = getRelationTypes(ctx.aggTypeList());
			if (!Types.getTypeVars(types).isEmpty()) {
				throw new RuntimeException("Cannot use type variables in the signature of a relation: " + name);
			}
			boolean isIdb = ctx.relType.getType() == FormulogLexer.OUTPUT;
			MutableRelationSymbol sym = symbolManager.createRelationSymbol(name, types.size(), isIdb,
					new FunctorType(types, BuiltInTypes.bool));
			setAggregate(sym, ctx.aggTypeList());
			for (AnnotationContext actx : ctx.annotation()) {
				switch (actx.getText()) {
				case "@bottomup":
					if (!sym.isIdbSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					sym.setBottomUp();
					break;
				case "@topdown":
					if (!sym.isIdbSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					sym.setTopDown();
					break;
				case "@external":
					if (!sym.isEdbSymbol()) {
						throw new RuntimeException("Annotation @external cannot be used for non-EDB predicate " + sym);
					}
					externalEdbs.add(sym);
					break;
				default:
					throw new RuntimeException("Unrecognized annotation for predicate " + sym + ": " + actx.getText());
				}
			}
			if (sym.isEdbSymbol()) {
				initialFacts.put(sym, new HashSet<>());
			} else {
				rules.put(sym, new HashSet<>());
			}
			return null;
		}

		@Override
		public Void visitTypeAlias(TypeAliasContext ctx) {
			Pair<TypeSymbol, List<TypeVar>> p = parseTypeDefLHS(ctx.typeDefLHS(), TypeSymbolType.TYPE_ALIAS);
			TypeSymbol sym = p.fst();
			List<TypeVar> typeVars = p.snd();
			Type type = ctx.type().accept(typeExtractor);
			if (!typeVars.containsAll(Types.getTypeVars(type))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			typeManager.registerAlias(new TypeAlias(sym, typeVars, type));
			return null;
		}

		@Override
		public Void visitTypeDecl(TypeDeclContext ctx) {
			List<Pair<TypeSymbol, List<TypeVar>>> lhss = map(ctx.typeDefLHS(),
					lhs -> parseTypeDefLHS(lhs, TypeSymbolType.NORMAL_TYPE));
			Iterator<TypeDefRHSContext> it = ctx.typeDefRHS().iterator();
			for (Pair<TypeSymbol, List<TypeVar>> p : lhss) {
				TypeSymbol sym = p.fst();
				List<TypeVar> typeVars = p.snd();
				AlgebraicDataType type = AlgebraicDataType.make(sym, new ArrayList<>(typeVars));
				TypeDefRHSContext rhs = it.next();
				if (rhs.adtDef() != null) {
					handleAdtDef(rhs.adtDef(), type, typeVars);
				} else {
					handleRecordDef(rhs.recordDef(), type, typeVars);
				}
			}
			return null;
		}

		private void handleAdtDef(AdtDefContext ctx, AlgebraicDataType type, List<TypeVar> typeVars) {
			Set<ConstructorScheme> constructors = new HashSet<>();
			for (ConstructorTypeContext ctc : ctx.constructorType()) {
				List<Type> typeArgs = map(ctc.typeList().type(), t -> t.accept(typeExtractor));
				ConstructorSymbol csym = symbolManager.createConstructorSymbol(ctc.ID().getText(), typeArgs.size(),
						ConstructorSymbolType.VANILLA_CONSTRUCTOR, new FunctorType(typeArgs, type));
				if (!typeVars.containsAll(Types.getTypeVars(typeArgs))) {
					throw new RuntimeException("Unbound type variable in definition of " + csym);
				}
				symbolManager.createConstructorSymbol("#is_" + csym.toString(), 1,
						ConstructorSymbolType.SOLVER_CONSTRUCTOR_TESTER, new FunctorType(type, BuiltInTypes.bool));
				List<ConstructorSymbol> getterSyms = new ArrayList<>();
				for (int i = 0; i < csym.getArity(); ++i) {
					FunctorType t = new FunctorType(type, typeArgs.get(i));
					String name = "#" + csym.toString() + "_" + (i + 1);
					getterSyms.add(symbolManager.createConstructorSymbol(name, 1,
							ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, t));
				}
				constructors.add(new ConstructorScheme(csym, typeArgs, getterSyms));
			}
			AlgebraicDataType.setConstructors(type.getSymbol(), typeVars, constructors);
		}

		private void handleRecordDef(RecordDefContext ctx, AlgebraicDataType type, List<TypeVar> typeVars) {
			List<Type> entryTypes = new ArrayList<>();
			List<ConstructorSymbol> getterSyms = new ArrayList<>();
			List<FunctionSymbol> labels = new ArrayList<>();
			int i = 0;
			for (RecordEntryDefContext entry : ctx.recordEntryDef()) {
				Type entryType = entry.type().accept(typeExtractor);
				entryTypes.add(entryType);
				FunctorType labelType = new FunctorType(type, entryType);
				FunctionSymbol label = symbolManager.createFunctionSymbol(entry.ID().getText(), 1, labelType);
				labels.add(label);
				final int j = i;
				functionDefManager.register(new FunctionDef() {

					@Override
					public FunctionSymbol getSymbol() {
						return label;
					}

					@Override
					public Term evaluate(Term[] args) throws EvaluationException {
						Constructor ctor = (Constructor) args[0];
						return ctor.getArgs()[j];
					}

				});
				ConstructorSymbol getter = symbolManager.createConstructorSymbol("#" + label, 1,
						ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, labelType);
				getterSyms.add(getter);
				recordLabels.put(label, new Pair<>(type, i));
				i++;
			}
			TypeSymbol sym = type.getSymbol();
			if (!typeVars.containsAll(Types.getTypeVars(entryTypes))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			FunctorType ctype = new FunctorType(entryTypes, type);
			RecordSymbol csym = symbolManager.createRecordSymbol("_rec_" + sym, entryTypes.size(), ctype, labels);
			ConstructorScheme ctor = new ConstructorScheme(csym, entryTypes, getterSyms);
			AlgebraicDataType.setConstructors(sym, typeVars, Collections.singleton(ctor));
			constructorLabels.put(csym, labels.toArray(new FunctionSymbol[0]));
		}

		private Pair<TypeSymbol, List<TypeVar>> parseTypeDefLHS(TypeDefLHSContext ctx, TypeSymbolType symType) {
			List<TypeVar> typeVars = map(ctx.TYPEVAR(), t -> TypeVar.get(t.getText()));
			TypeSymbol sym = symbolManager.createTypeSymbol(ctx.ID().getText(), typeVars.size(), symType);
			if (typeVars.size() != (new HashSet<>(typeVars)).size()) {
				throw new RuntimeException(
						"Cannot use the same type variable multiple times in a type declaration: " + sym);
			}
			return new Pair<>(sym, typeVars);
		}

		@Override
		public Void visitUninterpSortDecl(UninterpSortDeclContext ctx) {
			parseTypeDefLHS(ctx.typeDefLHS(), TypeSymbolType.UNINTERPRETED_SORT);
			return null;
		}

		@Override
		public Void visitUninterpFunDecl(UninterpFunDeclContext ctx) {
			ConstructorTypeContext ctc = ctx.constructorType();
			List<Type> typeArgs = map(ctc.typeList().type(), t -> t.accept(typeExtractor));
			Type type = ctx.type().accept(typeExtractor);
			ConstructorSymbol csym = symbolManager.createConstructorSymbol(ctc.ID().getText(), typeArgs.size(),
					ConstructorSymbolType.SOLVER_UNINTERPRETED_FUNCTION, new FunctorType(typeArgs, type));
			if (!(type instanceof AlgebraicDataType)
					|| !((AlgebraicDataType) type).getSymbol().equals(BuiltInTypeSymbol.SMT_TYPE)) {
				throw new RuntimeException("Uninterpreted function must have an "
						+ BuiltInTypeSymbol.SMT_TYPE.toString() + " type: " + csym);
			}
			if (!Types.getTypeVars(typeArgs).isEmpty() || !Types.getTypeVars(type).isEmpty()) {
				throw new RuntimeException("Unbound type variable in definition of " + csym);
			}
			uninterpFuncSymbols.add(csym);
			return null;
		}

		@Override
		public Void visitClauseStmt(ClauseStmtContext ctx) {
			List<ComplexLiteral> head = atomListContextToAtomList(ctx.clause().head);
			List<ComplexLiteral> body = atomListContextToAtomList(ctx.clause().body);
			List<BasicRule> newRules = makeRules(head, body);
			for (BasicRule rule : newRules) {
				RelationSymbol sym = rule.getHead().getSymbol();
				if (!sym.isIdbSymbol()) {
					throw new RuntimeException("Cannot define a rule for a non-IDB symbol: " + sym);
				}
				Util.lookupOrCreate(rules, sym, () -> new HashSet<>()).add(rule);
			}
			return null;
		}

		private BasicRule makeRule(ComplexLiteral head, List<ComplexLiteral> body) {
			List<ComplexLiteral> newBody = new ArrayList<>(body);
			if (!(head instanceof UserPredicate)) {
				throw new RuntimeException("Cannot create rule with non-user predicate in head: " + head);
			}
			try {
				return varChecker.checkRule((BasicRule.make((UserPredicate) head, newBody)));
			} catch (ParseException e) {
				throw new RuntimeException(e);
			}
		}

		private List<BasicRule> makeRules(List<ComplexLiteral> head, List<ComplexLiteral> body) {
			List<BasicRule> rules = new ArrayList<>();
			for (ComplexLiteral hd : head) {
				rules.add(makeRule(hd, body));
			}
			return rules;
		}

		// private Atom removeFuncCallsFromAtom(Atom a, List<Atom> acc) {
		// Term[] args = a.getArgs();
		// Term[] newArgs = new Term[args.length];
		// for (int i = 0; i < args.length; ++i) {
		// newArgs[i] = args[i].visit(new TermVisitor<Void, Term>() {
		//
		// @Override
		// public Term visit(Var var, Void in) {
		// return var;
		// }
		//
		// @Override
		// public Term visit(Constructor constr, Void in) {
		// Term[] args = constr.getArgs();
		// Term[] newArgs = new Term[args.length];
		// for (int i = 0; i < args.length; ++i) {
		// newArgs[i] = args[i].visit(this, null);
		// }
		// return constr.copyWithNewArgs(newArgs);
		// }
		//
		// @Override
		// public Term visit(Primitive<?> prim, Void in) {
		// return prim;
		// }
		//
		// @Override
		// public Term visit(Expr expr, Void in) {
		// Var x = Var.getFresh(false);
		// acc.add(Atoms.getPositive(BuiltInPredicateSymbol.UNIFY, new Term[] { x, expr
		// }));
		// return x;
		// }
		//
		// }, null);
		// }
		// return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
		// }

		@Override
		public Void visitFactStmt(FactStmtContext ctx) {
			UserPredicate fact = (UserPredicate) ctx.fact().atom().accept(atomExtractor);
			RelationSymbol sym = fact.getSymbol();
			if (sym.isIdbSymbol()) {
				BasicRule rule = makeRule(fact, Collections.emptyList());
				rules.get(sym).add(rule);
			} else {
				try {
					Term[] args = varChecker.checkFact(fact.getArgs());
					initialFacts.get(sym).add(args);
				} catch (ParseException e) {
					throw new RuntimeException(e);
				}
			}
			return null;
		}

		@Override
		public Void visitQueryStmt(QueryStmtContext ctx) {
			ComplexLiteral a = ctx.query().atom().accept(atomExtractor);
			if (!(a instanceof UserPredicate)) {
				throw new RuntimeException("Query must be for a user-defined predicate: " + a);
			}
			if (query != null) {
				throw new RuntimeException("Cannot have multiple queries in the same program: " + query + " and " + a);
			}
			UserPredicate q = (UserPredicate) a;
			try {
				query = UserPredicate.make(q.getSymbol(), varChecker.checkFact(q.getArgs()), q.isNegated());
			} catch (ParseException e) {
				throw new RuntimeException("Problem with query " + query + ": " + e.getMessage());
			}
			return null;
		}

		List<ComplexLiteral> atomListContextToAtomList(AtomListContext ctx) {
			return map(ctx.atom(), a -> a.accept(atomExtractor));
		}

		private Term extract(TermContext ctx) {
			return ctx.accept(termExtractor);
		}

		private final FormulogVisitor<Term> termExtractor = new FormulogBaseVisitor<Term>() {

			public Term extract(TermContext ctx) {
				return ctx.accept(this);
			}

			private boolean inFormula;

			private void assertInFormula(String msg) {
				if (!inFormula) {
					throw new RuntimeException(msg);
				}
			}

			private void assertNotInFormula(String msg) {
				if (inFormula) {
					throw new RuntimeException(msg);
				}
			}

			private void toggleInFormula() {
				inFormula = !inFormula;
			}

			@Override
			public Term visitHoleTerm(HoleTermContext ctx) {
				return Var.makeHole();
			}

			@Override
			public Term visitVarTerm(VarTermContext ctx) {
				String name = ctx.VAR().getText();
				return Var.make(name);
			}

			@Override
			public Term visitStringTerm(StringTermContext ctx) {
				String s = ctx.QSTRING().getText();
				return StringTerm.make(s.substring(1, s.length() - 1));
			}

			@Override
			public Term visitConsTerm(ConsTermContext ctx) {
				List<Term> args = map(ctx.term(), t -> t.accept(this));
				return Constructors.make(BuiltInConstructorSymbol.CONS, args.toArray(Terms.emptyArray()));
			}

			@Override
			public Term visitIndexedFunctor(IndexedFunctorContext ctx) {
				String name = ctx.id.getText();
				List<Integer> indices = getIndices(ctx.index());
				Symbol sym;
				if (indices.isEmpty()) {
					sym = symbolManager.lookupSymbol(name);
				} else {
					Pair<IndexedConstructorSymbol, List<Integer>> p = symbolManager.lookupIndexedConstructorSymbol(name,
							indices);
					sym = p.fst();
					indices = p.snd();
				}
				Term[] args = termContextsToTerms(ctx.termArgs().term());
				Term[] expandedArgs = new Term[args.length + indices.size()];
				System.arraycopy(args, 0, expandedArgs, 0, args.length);
				Iterator<Integer> it = indices.iterator();
				for (int i = args.length; i < expandedArgs.length; ++i) {
					Integer idx = it.next();
					Term t;
					if (idx == null) {
						t = Var.fresh();
					} else {
						ConstructorSymbol csym = symbolManager.lookupIndexConstructorSymbol(idx);
						t = Constructors.make(csym, Terms.singletonArray(I32.make(idx)));
					}
					expandedArgs[i] = t;
				}
				Term t = makeFunctor(sym, expandedArgs);
				// For a couple constructors, we want to make sure that their arguments are
				// forced to be non-formula types. For example, the constructor bv_const needs
				// to take something of type i32, not i32 expr.
				if (sym instanceof IndexedConstructorSymbol) {
					switch ((IndexedConstructorSymbol) sym) {
					case BV_BIG_CONST:
					case BV_CONST:
					case FP_BIG_CONST:
					case FP_CONST:
						t = makeExitFormula(t);
					default:
						break;
					}
				}
				return t;
			}

			private Term makeFunctor(Symbol sym, Term[] args) {
				if (sym instanceof RelationSymbol) {
					FunctionSymbol newSym = symbolManager
							.createPredicateFunctionSymbolPlaceholder((RelationSymbol) sym);
					return functionCallFactory.make(newSym, args);
				} else if (sym instanceof FunctionSymbol) {
					Term t = functionCallFactory.make((FunctionSymbol) sym, args);
					if (sym.getArity() > 0) {
						assertNotInFormula("Cannot invoke a non-nullary function from within a formula: " + t);
					}
					return t;
				} else if (sym instanceof ConstructorSymbol) {
					ConstructorSymbol csym = (ConstructorSymbol) sym;
					Term t = Constructors.make(csym, args);
					if (csym.isSolverConstructorSymbol()) {
						assertInFormula(
								"Can only use an uninterpreted function or solver expression within a formula: " + t);
					}
					return t;
				} else {
					throw new RuntimeException(
							"Cannot create a term with non-constructor, non-function symbol " + sym + ".");
				}
			}

			@Override
			public Term visitSmtEqTerm(SmtEqTermContext ctx) {
				Type type = ctx.type().accept(typeExtractor);
				if (isSolverUnfriendlyType(type)) {
					throw new RuntimeException(
							"Cannot create an smt_eq with a type that contains a type variable, an smt type, or a sym type: "
									+ ctx.getText());
				}
				ConstructorSymbol sym = symbolManager.lookupSmtEqSymbol(type);
				Term[] args = termContextsToTerms(ctx.termArgs().term());
				return Constructors.make(sym, args);
			}

			@Override
			public Term visitTupleTerm(TupleTermContext ctx) {
				Term[] args = termContextsToTerms(ctx.tuple().term());
				return Constructors.make(symbolManager.lookupTupleSymbol(args.length), args);
			}

			private final Pattern hex = Pattern.compile("0x([0-9a-fA-F]+)[lL]?");

			@Override
			public Term visitI32Term(I32TermContext ctx) {
				Matcher m = hex.matcher(ctx.val.getText());
				int n;
				if (m.matches()) {
					n = Integer.parseUnsignedInt(m.group(1).toUpperCase(), 16);
				} else {
					n = Integer.parseInt(ctx.val.getText());
				}
				return I32.make(n);
			}

			@Override
			public Term visitI64Term(I64TermContext ctx) {
				Matcher m = hex.matcher(ctx.val.getText());
				long n;
				if (m.matches()) {
					n = Long.parseUnsignedLong(m.group(1).toUpperCase(), 16);
				} else {
					// Long.parseLong does not allow trailing l or L.
					String text = ctx.val.getText();
					String sub = text.substring(0, text.length() - 1);
					n = Long.parseLong(sub);
				}
				return I64.make(n);
			}

			@Override
			public Term visitFloatTerm(FloatTermContext ctx) {
				return FP32.make(Float.parseFloat(ctx.val.getText()));
			}

			@Override
			public Term visitDoubleTerm(DoubleTermContext ctx) {
				return FP64.make(Double.parseDouble(ctx.val.getText()));
			}

			@Override
			public Term visitSpecialFPTerm(SpecialFPTermContext ctx) {
				switch (ctx.val.getType()) {
				case FormulogParser.FP32_NAN:
					return FP32.make(Float.NaN);
				case FormulogParser.FP32_NEG_INFINITY:
					return FP32.make(Float.NEGATIVE_INFINITY);
				case FormulogParser.FP32_POS_INFINITY:
					return FP32.make(Float.POSITIVE_INFINITY);
				case FormulogParser.FP64_NAN:
					return FP64.make(Double.NaN);
				case FormulogParser.FP64_NEG_INFINITY:
					return FP64.make(Double.NEGATIVE_INFINITY);
				case FormulogParser.FP64_POS_INFINITY:
					return FP64.make(Double.POSITIVE_INFINITY);
				}
				throw new AssertionError();
			}

			@Override
			public Term visitRecordTerm(RecordTermContext ctx) {
				Pair<ConstructorSymbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
				ConstructorSymbol csym = p.fst();
				Map<Integer, Term> argMap = p.snd();
				Term[] args = new Term[csym.getArity()];
				if (args.length != argMap.keySet().size()) {
					throw new RuntimeException("Missing label(s) when creating record of type " + csym);
				}
				for (int i = 0; i < args.length; i++) {
					args[i] = argMap.get(i);
				}
				return Constructors.make(csym, args);
			}

			@Override
			public Term visitRecordUpdateTerm(RecordUpdateTermContext ctx) {
				Pair<ConstructorSymbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
				ConstructorSymbol csym = p.fst();
				Map<Integer, Term> argMap = p.snd();
				Term[] args = new Term[csym.getArity()];
				FunctionSymbol[] labels = constructorLabels.get(csym);
				Term orig = extract(ctx.term());
				for (int i = 0; i < args.length; ++i) {
					Term t = argMap.get(i);
					if (t == null) {
						FunctionSymbol label = labels[i];
						t = functionCallFactory.make(label, Terms.singletonArray(orig));
					}
					args[i] = t;
				}
				return Constructors.make(csym, args);
			}

			private Pair<ConstructorSymbol, Map<Integer, Term>> handleRecordEntries(List<RecordEntryContext> entries) {
				AlgebraicDataType type = null;
				Map<Integer, Term> argMap = new HashMap<>();
				for (RecordEntryContext entry : entries) {
					Symbol label = symbolManager.lookupSymbol(entry.ID().getText());
					Pair<AlgebraicDataType, Integer> p = recordLabels.get(label);
					if (p == null) {
						throw new RuntimeException(label + " is not a record label");
					}
					AlgebraicDataType type2 = p.fst();
					if (type == null) {
						type = type2;
					} else if (!type.equals(type2)) {
						throw new RuntimeException("Cannot use label " + label + " in a record of type " + type);
					}
					if (argMap.putIfAbsent(p.snd(), extract(entry.term())) != null) {
						throw new RuntimeException(
								"Cannot use the same label " + label + " multiple times when creating a record");
					}
				}
				ConstructorSymbol csym = type.getConstructors().iterator().next().getSymbol();
				return new Pair<>(csym, argMap);
			}

			@Override
			public Term visitUnopTerm(UnopTermContext ctx) {
				Term t = ctx.term().accept(this);
				FunctionSymbol sym = tokenToUnopSym(ctx.op.getType());
				if (sym == null) {
					t = makeNonFunctionUnop(ctx.op.getType(), t);
				} else {
					t = functionCallFactory.make(sym, new Term[] { t });
				}
				if (t == null) {
					throw new AssertionError("Unrecognized unop: " + ctx.getText());
				}
				assertNotInFormula("Cannot invoke a unop from within a formula: " + ctx.getText());
				return t;
			}

			private Term makeNonFunctionUnop(int tokenType, Term t) {
				switch (tokenType) {
				case FormulogParser.BANG:
					return makeBoolMatch(t, Constructors.falseTerm(), Constructors.trueTerm());
				default:
					return null;
				}
			}

			private Term makeBoolMatch(Term matchee, Term ifTrue, Term ifFalse) {
				MatchClause matchTrue = MatchClause.make(Constructors.trueTerm(), ifTrue);
				MatchClause matchFalse = MatchClause.make(Constructors.falseTerm(), ifFalse);
				return MatchExpr.make(matchee, Arrays.asList(matchTrue, matchFalse));
			}

			private FunctionSymbol tokenToUnopSym(int tokenType) {
				switch (tokenType) {
				case FormulogParser.MINUS:
					return BuiltInFunctionSymbol.I32_NEG;
				default:
					return null;
				}
			}

			private FunctionSymbol tokenToBinopSym(int tokenType) {
				switch (tokenType) {
				case FormulogParser.MUL:
					return BuiltInFunctionSymbol.I32_MUL;
				case FormulogParser.DIV:
					return BuiltInFunctionSymbol.I32_DIV;
				case FormulogParser.REM:
					return BuiltInFunctionSymbol.I32_REM;
				case FormulogParser.PLUS:
					return BuiltInFunctionSymbol.I32_ADD;
				case FormulogParser.MINUS:
					return BuiltInFunctionSymbol.I32_SUB;
				case FormulogParser.AMP:
					return BuiltInFunctionSymbol.I32_AND;
				case FormulogParser.CARET:
					return BuiltInFunctionSymbol.I32_XOR;
				case FormulogParser.EQ:
					return BuiltInFunctionSymbol.BEQ;
				case FormulogParser.NEQ:
					return BuiltInFunctionSymbol.BNEQ;
				case FormulogParser.LT:
					return BuiltInFunctionSymbol.I32_LT;
				case FormulogParser.LTE:
					return BuiltInFunctionSymbol.I32_LE;
				case FormulogParser.GT:
					return BuiltInFunctionSymbol.I32_GT;
				case FormulogParser.GTE:
					return BuiltInFunctionSymbol.I32_GE;
				default:
					return null;
				}
			}

			private Term makeNonFunctionBinop(int tokenType, Term lhs, Term rhs) {
				switch (tokenType) {
				case FormulogParser.AMPAMP:
					return makeBoolMatch(lhs, rhs, Constructors.falseTerm());
				case FormulogParser.BARBAR:
					return makeBoolMatch(lhs, Constructors.trueTerm(), rhs);
				default:
					return null;
				}
			}

			@Override
			public Term visitBinopTerm(BinopTermContext ctx) {
				Term[] args = { extract(ctx.term(0)), extract(ctx.term(1)) };
				FunctionSymbol sym = tokenToBinopSym(ctx.op.getType());
				Term t;
				if (sym == null) {
					t = makeNonFunctionBinop(ctx.op.getType(), args[0], args[1]);
				} else {
					t = functionCallFactory.make(sym, args);
				}
				if (t == null) {
					throw new AssertionError("Unrecognized binop: " + ctx.getText());
				}
				assertNotInFormula("Cannot invoke a binop from within a formula: " + ctx.getText());
				return t;
			}

			@Override
			public Term visitListTerm(ListTermContext ctx) {
				Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
				List<TermContext> ctxs = new ArrayList<>(ctx.list().term());
				Collections.reverse(ctxs);
				for (TermContext tc : ctxs) {
					t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { extract(tc), t });
				}
				return t;
			}

			@Override
			public Term visitParensTerm(ParensTermContext ctx) {
				return extract(ctx.term());
			}

			private Term makeExitFormula(Term t) {
				return Constructors.make(BuiltInConstructorSymbol.EXIT_FORMULA, Terms.singletonArray(t));
			}

			private Term makeEnterFormula(Term t) {
				return Constructors.make(BuiltInConstructorSymbol.ENTER_FORMULA, Terms.singletonArray(t));
			}

			@Override
			public Term visitFormulaTerm(FormulaTermContext ctx) {
				assertNotInFormula("Cannot nest a formula within a formula: " + ctx.getText());
				toggleInFormula();
				Term t = extract(ctx.term());
				t = Constructors.make(BuiltInConstructorSymbol.ENTER_FORMULA, Terms.singletonArray(t));
				toggleInFormula();
				return t;
			}

			@Override
			public Term visitNotFormula(NotFormulaContext ctx) {
				assertInFormula("~ can only be used from within a formula: " + ctx.getText());
				Term t = extract(ctx.term());
				return Constructors.make(BuiltInConstructorSymbol.FORMULA_NOT, Terms.singletonArray(t));
			}

			@Override
			public Term visitBinopFormula(BinopFormulaContext ctx) {
				assertInFormula("Formula binop can only be used from within a formula: " + ctx.getText());
				Term[] args = termContextsToTerms(ctx.term());
				ConstructorSymbol sym;
				switch (ctx.op.getType()) {
				case FormulogParser.FORMULA_EQ:
				case FormulogParser.IFF:
					sym = BuiltInConstructorSymbol.FORMULA_EQ;
					break;
				case FormulogParser.IMP:
					sym = BuiltInConstructorSymbol.FORMULA_IMP;
					break;
				case FormulogParser.AND:
					sym = BuiltInConstructorSymbol.FORMULA_AND;
					break;
				case FormulogParser.OR:
					sym = BuiltInConstructorSymbol.FORMULA_OR;
					break;
				default:
					throw new AssertionError();
				}
				return Constructors.make(sym, args);
			}

			@Override
			public Term visitLetFormula(LetFormulaContext ctx) {
				assertInFormula("Can only use a let formula within a formula: " + ctx.getText());
				Term[] args = termContextsToTerms(ctx.term());
				args[1] = makeEnterFormula(args[1]);
				args[2] = makeEnterFormula(args[2]);
				return makeExitFormula(Constructors.make(BuiltInConstructorSymbol.FORMULA_LET, args));
			}

			@Override
			public Term visitQuantifiedFormula(QuantifiedFormulaContext ctx) {
				assertInFormula("Can only use a quantified formula within a formula: " + ctx.getText());
				Term[] args = new Term[3];
				args[0] = parseFormulaVarList(ctx.variables);
				args[1] = makeEnterFormula(extract(ctx.boundTerm));
				if (ctx.pattern != null) {
					args[2] = Constructors.make(BuiltInConstructorSymbol.SOME,
							Terms.singletonArray(makeEnterFormula(parseHeterogeneousList(ctx.pattern))));
				} else {
					args[2] = Constructors.makeZeroAry(BuiltInConstructorSymbol.NONE);
				}
				ConstructorSymbol sym;
				switch (ctx.quantifier.getType()) {
				case FormulogParser.FORALL:
					sym = BuiltInConstructorSymbol.FORMULA_FORALL;
					break;
				case FormulogParser.EXISTS:
					sym = BuiltInConstructorSymbol.FORMULA_EXISTS;
					break;
				default:
					throw new AssertionError();
				}
				return makeExitFormula(Constructors.make(sym, args));
			}

			private Term parseFormulaVarList(NonEmptyTermListContext ctx) {
				return parseNonEmptyTermList(ctx, BuiltInConstructorSymbol.FORMULA_VAR_LIST_NIL,
						BuiltInConstructorSymbol.FORMULA_VAR_LIST_CONS);
			}

			private Term parseHeterogeneousList(NonEmptyTermListContext ctx) {
				return parseNonEmptyTermList(ctx, BuiltInConstructorSymbol.HETEROGENEOUS_LIST_NIL,
						BuiltInConstructorSymbol.HETEROGENEOUS_LIST_CONS);
			}

			private Term parseNonEmptyTermList(NonEmptyTermListContext ctx, ConstructorSymbol nil,
					ConstructorSymbol cons) {
				Term t = Constructors.makeZeroAry(nil);
				List<TermContext> ctxs = new ArrayList<>(ctx.term());
				Collections.reverse(ctxs);
				for (TermContext tc : ctxs) {
					t = Constructors.make(cons, new Term[] { extract(tc), t });
				}
				return t;
			}

			@Override
			public Term visitIteTerm(IteTermContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				if (inFormula) {
					return Constructors.make(BuiltInConstructorSymbol.FORMULA_ITE, args);
				} else {
					return makeBoolMatch(args[0], args[1], args[2]);
				}
			}

			@Override
			public Term visitConstSymFormula(ConstSymFormulaContext ctx) {
				Type type = ctx.type().accept(typeExtractor);
				Term id = StringTerm.make(ctx.id.getText().substring(1));
				return extractSolverSymbol(id, type);
			}

			@Override
			public Term visitTermSymFormula(TermSymFormulaContext ctx) {
				Type type = ctx.type().accept(typeExtractor);
				Term id = extract(ctx.term());
				return extractSolverSymbol(id, type);
			}

			private Term extractSolverSymbol(Term id, Type type) {
				if (isSolverUnfriendlyType(type)) {
					throw new RuntimeException(
							"Cannot create solver variable with a type that contains a type variable, an smt type, or a sym type: "
									+ type);
				}
				ConstructorSymbol sym = symbolManager.lookupSolverSymbol(type);
				return makeExitFormula(Constructors.make(sym, Terms.singletonArray(id)));
			}

			private boolean isSolverUnfriendlyType(Type type) {
				return type.visit(new TypeVisitor<Void, Boolean>() {

					@Override
					public Boolean visit(TypeVar typeVar, Void in) {
						return true;
					}

					@Override
					public Boolean visit(AlgebraicDataType algebraicType, Void in) {
						Symbol sym = algebraicType.getSymbol();
						if (sym.equals(BuiltInTypeSymbol.SMT_TYPE) || sym.equals(BuiltInTypeSymbol.SYM_TYPE)) {
							return true;
						}
						for (Type ty : algebraicType.getTypeArgs()) {
							if (ty.visit(this, in)) {
								return true;
							}
						}
						return false;
					}

					@Override
					public Boolean visit(OpaqueType opaqueType, Void in) {
						throw new AssertionError();
					}

					@Override
					public Boolean visit(TypeIndex typeIndex, Void in) {
						return false;
					}

				}, null);
			}

			public Term visitOutermostCtor(OutermostCtorContext ctx) {
				Symbol ctor = symbolManager.lookupSymbol(ctx.ID().getText());
				if (!(ctor instanceof ConstructorSymbol)) {
					throw new RuntimeException("Cannot use non-constructor symbol " + ctor + " in a `not` term.");
				}

				// we'll call a fixed function name
				FunctorType ctorType = ((ConstructorSymbol) ctor).getCompileTimeType();
				String name = "not%" + ctor;
				FunctionSymbol isNotFun;
				if (symbolManager.hasSymbol(name)) {
					isNotFun = (FunctionSymbol) symbolManager.lookupSymbol(name);
				} else {
					isNotFun = symbolManager.createFunctionSymbol("not%" + ctor, 1,
							new FunctorType(ctorType.getRetType(), BuiltInTypes.bool));
				}

				// generate the function if needed
				if (!functionDefManager.hasDefinition(isNotFun)) {
					functionDefManager.register(new FunctionDef() {

						@Override
						public FunctionSymbol getSymbol() {
							return isNotFun;
						}

						@Override
						public Term evaluate(Term[] args) throws EvaluationException {
							Constructor c = (Constructor) args[0];
							if (c.getSymbol().equals(ctor)) {
								return Constructors.falseTerm();
							}
							return Constructors.trueTerm();
						}

					});
				}

				Term arg = extract(ctx.term());
				return functionCallFactory.make(isNotFun, Terms.singletonArray(arg));
			}

			@Override
			public Term visitMatchExpr(MatchExprContext ctx) {
				Term guard = ctx.term().accept(this);
				List<MatchClause> matches = new ArrayList<>();
				for (MatchClauseContext mcc : ctx.matchClause()) {
					Term rhs = extract(mcc.rhs);
					for (TermContext pc : mcc.patterns().term()) {
						Term pattern = extract(pc);
						matches.add(MatchClause.make(pattern, rhs));
					}
				}
				return MatchExpr.make(guard, matches);
			}

			@Override
			public Term visitLetExpr(LetExprContext ctx) {
				List<Term> ts = map(ctx.letBind().term(), StmtProcessor.this::extract);
				Term t;
				if (ts.size() > 1) {
					t = Constructors.make(symbolManager.lookupTupleSymbol(ts.size()), ts.toArray(Terms.emptyArray()));
				} else {
					t = ts.get(0);
				}
				Term assign = ctx.assign.accept(this);
				Term body = ctx.body.accept(this);
				MatchClause m = MatchClause.make(t, body);
				return MatchExpr.make(assign, Collections.singletonList(m));
			}

			@Override
			public Term visitIfExpr(IfExprContext ctx) {
				Term guard = ctx.guard.accept(this);
				Term thenExpr = ctx.thenExpr.accept(this);
				Term elseExpr = ctx.elseExpr.accept(this);
				List<MatchClause> branches = new ArrayList<>();
				branches.add(MatchClause.make(Constructors.trueTerm(), thenExpr));
				branches.add(MatchClause.make(Constructors.falseTerm(), elseExpr));
				return MatchExpr.make(guard, branches);
			}

		};

		private Term[] termContextsToTerms(List<TermContext> ctxs) {
			return map(ctxs, this::extract).toArray(Terms.emptyArray());
		}

		private final FormulogVisitor<ComplexLiteral> atomExtractor = new FormulogBaseVisitor<ComplexLiteral>() {

			private ComplexLiteral extractAtom(PredicateContext ctx, boolean negated) {
				Term[] args = termContextsToTerms(ctx.termArgs().term());
				Symbol sym = symbolManager.lookupSymbol(ctx.ID().getText());
				if (sym.getArity() != args.length) {
					throw new RuntimeException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
							+ Arrays.toString(args) + " have length " + args.length);
				}
				if (sym instanceof FunctionSymbol) {
					Term f = functionCallFactory.make((FunctionSymbol) sym, args);
					return ComplexLiterals.unifyWithBool(f, !negated);
				}
				if (sym instanceof ConstructorSymbol) {
					Term c = Constructors.make((ConstructorSymbol) sym, args);
					return ComplexLiterals.unifyWithBool(c, !negated);
				}
				if (sym instanceof RelationSymbol) {
					return UserPredicate.make((RelationSymbol) sym, args, negated);
				}
				throw new AssertionError("impossible");
			}

			@Override
			public ComplexLiteral visitNormalAtom(NormalAtomContext ctx) {
				return extractAtom(ctx.predicate(), false);
			}

			@Override
			public ComplexLiteral visitNegatedAtom(NegatedAtomContext ctx) {
				return extractAtom(ctx.predicate(), true);
			}

			@Override
			public ComplexLiteral visitUnification(UnificationContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				return UnificationPredicate.make(args[0], args[1], false);
			}

			@Override
			public ComplexLiteral visitDisunification(DisunificationContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				return UnificationPredicate.make(args[0], args[1], true);
			}

			@Override
			public ComplexLiteral visitTermAtom(TermAtomContext ctx) {
				Term arg = extract(ctx.term());
				return ComplexLiterals.unifyWithBool(arg, true);
			}

		};

		private Set<Term[]> readEdbFromFile(RelationSymbol sym) throws ParseException {
			Set<Term[]> facts = new HashSet<>();
			facts.addAll(initialFacts.get(sym));
			Path path = inputDir.resolve(sym.toString() + ".csv");
			try {
				Stream<String> lines;
				lines = Files.lines(path);
				for (Iterator<String> it = lines.iterator(); it.hasNext();) {
					readLineFromCsv(sym, new StringReader(it.next()), facts);
				}
				lines.close();
			} catch (Exception e) {
				throw new ParseException("Exception when extracting facts from " + path + ":\n" + e);
			}
			return facts;
		}

		private void readLineFromCsv(RelationSymbol sym, Reader r, Set<Term[]> facts) throws ParseException {
			FormulogParser parser = getParser(r);
			Term[] args = new Term[sym.getArity()];
			for (int i = 0; i < args.length; i++) {
				args[i] = extract(parser.term());
			}
			args = varChecker.checkFact(args);
			facts.add(args);
		}

		// XXX It would probably be better just to force everything to go
		// through a type manager and have that keep track of all of the types.
		private Set<TypeSymbol> findTypes() {
			TypeFinder tf = new TypeFinder();
			for (FunctionSymbol sym : functionDefManager.getFunctionSymbols()) {
				tf.exploreFunction(functionDefManager.lookup(sym));
			}
			for (RelationSymbol sym : initialFacts.keySet()) {
				tf.exploreFunctorType(sym.getCompileTimeType());
			}
			for (RelationSymbol sym : rules.keySet()) {
				tf.exploreFunctorType(sym.getCompileTimeType());
				for (BasicRule r : rules.get(sym)) {
					tf.exploreRule(r);
				}
			}
			return tf.getTypes();
		}
		
		public BasicProgram getProgram() throws ParseException {
			if (!externalEdbs.isEmpty()) {
				ExecutorService exec = Executors.newFixedThreadPool(Configuration.parallelism);
				Map<RelationSymbol, Future<Set<Term[]>>> futures = new HashMap<>();
				for (RelationSymbol sym : externalEdbs) {
					Future<Set<Term[]>> fut = exec.submit(new Callable<Set<Term[]>>() {

						@Override
						public Set<Term[]> call() throws Exception {
							return readEdbFromFile(sym);
						}

					});
					futures.put(sym, fut);
				}
				exec.shutdown();
				try {
					Util.fillMapWithFutures(futures, initialFacts);
				} catch (InterruptedException | ExecutionException e) {
					throw new ParseException(e);
				}
			}
			Set<TypeSymbol> typeSymbols = Collections.unmodifiableSet(findTypes());
			return new BasicProgram() {

				@Override
				public Set<FunctionSymbol> getFunctionSymbols() {
					return functionDefManager.getFunctionSymbols();
				}

				@Override
				public Set<RelationSymbol> getFactSymbols() {
					return Collections.unmodifiableSet(initialFacts.keySet());
				}

				@Override
				public Set<RelationSymbol> getRuleSymbols() {
					return Collections.unmodifiableSet(rules.keySet());
				}

				@Override
				public FunctionDef getDef(FunctionSymbol sym) {
					return functionDefManager.lookup(sym);
				}

				@Override
				public Set<Term[]> getFacts(RelationSymbol sym) {
					if (!sym.isEdbSymbol()) {
						throw new IllegalArgumentException();
					}
					if (!initialFacts.containsKey(sym)) {
						throw new IllegalArgumentException();
					}
					return initialFacts.get(sym);
				}

				@Override
				public Set<BasicRule> getRules(RelationSymbol sym) {
					if (!sym.isIdbSymbol()) {
						throw new IllegalArgumentException();
					}
					if (!rules.containsKey(sym)) {
						throw new IllegalArgumentException();
					}
					return rules.get(sym);
				}

				@Override
				public SymbolManager getSymbolManager() {
					return symbolManager;
				}

				@Override
				public boolean hasQuery() {
					return query != null;
				}

				@Override
				public UserPredicate getQuery() {
					return query;
				}

				@Override
				public FunctionCallFactory getFunctionCallFactory() {
					return functionCallFactory;
				}

				@Override
				public Set<ConstructorSymbol> getUninterpretedFunctionSymbols() {
					return Collections.unmodifiableSet(uninterpFuncSymbols);
				}

				@Override
				public Set<TypeSymbol> getTypeSymbols() {
					return typeSymbols;
				}

			};
		}
	};

}
