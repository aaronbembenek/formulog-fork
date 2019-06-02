package edu.harvard.seas.pl.formulog.eval;

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

import static org.junit.Assert.fail;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.junit.Test;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.eval.Interpreter;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;
import edu.harvard.seas.pl.formulog.validating.Validator;

public class EvaluationTest {

	void test(String file) {
		boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
		try {
			InputStream is = getClass().getClassLoader().getResourceAsStream(file);
			if (is == null) {
				throw new FileNotFoundException(file + " not found");
			}
			Pair<Program, Atom> p = (new Parser()).parse(new InputStreamReader(is));
			Program prog = p.fst();
			assert p.snd() == null;
			prog = (new TypeChecker(prog, p.snd())).typeCheck();
			ValidProgram vprog = (new Validator(prog)).validate();
			Interpreter interp = new Interpreter(vprog);
			IndexedFactDB db = interp.run(1);
			boolean ok = false;
			for (Symbol sym : db.getSymbols()) {
				if (sym.toString().equals("ok")) {
					ok = true;
					break;
				}
			}
			if (!ok && !isBad) {
				fail("Test failed for a good program");
			}
			if (ok && isBad) {
				fail("Test succeeded for a bad program");
			}
		} catch (Exception e) {
			fail("Unexpected exception: " + e);
		}
	}

	@Test
	public void test018() {
		test("test018_ok.flg");
	}

	@Test
	public void test019() {
		test("test019_ok.flg");
	}

	@Test
	public void test020() {
		test("test020_ok.flg");
	}

	@Test
	public void test021() {
		test("test021_ok.flg");
	}

	@Test
	public void test022() {
		test("test022_ok.flg");
	}

	@Test
	public void test023() {
		test("test023_ok.flg");
	}

	@Test
	public void test024() {
		test("test024_ok.flg");
	}

	@Test
	public void test026() {
		test("test026_ok.flg");
	}

	@Test
	public void test027() {
		test("test027_ok.flg");
	}

	@Test
	public void test029() {
		test("test029_ok.flg");
	}

	@Test
	public void test030() {
		test("test030_ok.flg");
	}

	@Test
	public void test032() {
		test("test032_ok.flg");
	}

	@Test
	public void test033() {
		test("test033_ok.flg");
	}

	@Test
	public void test034() {
		test("test034_ok.flg");
	}

	@Test
	public void test035() {
		test("test035_ok.flg");
	}

	@Test
	public void test037() {
		test("test037_ok.flg");
	}

	@Test
	public void test038() {
		test("test038_ok.flg");
	}

	@Test
	public void test039() {
		test("test039_ok.flg");
	}

	@Test
	public void test040() {
		test("test040_ok.flg");
	}

	@Test
	public void test041() {
		test("test041_ok.flg");
	}

	@Test
	public void test043() {
		test("test043_ok.flg");
	}

	@Test
	public void test044() {
		test("test044_ok.flg");
	}

	@Test
	public void test045() {
		test("test045_ok.flg");
	}

	@Test
	public void test046() {
		test("test046_ok.flg");
	}

	@Test
	public void test047() {
		test("test047_ok.flg");
	}

	@Test
	public void test048() {
		test("test048_ok.flg");
	}

	@Test
	public void test056() {
		test("test056_ok.flg");
	}

	@Test
	public void test057() {
		test("test057_ok.flg");
	}

	@Test
	public void test058() {
		test("test058_ok.flg");
	}

	@Test
	public void test061() {
		test("test061_ok.flg");
	}

	@Test
	public void test062() {
		test("test062_ok.flg");
	}

	@Test
	public void test063() {
		test("test063_ok.flg");
	}

	@Test
	public void test064() {
		test("test064_ok.flg");
	}

	@Test
	public void test065() {
		test("test065_ok.flg");
	}

	@Test
	public void test066() {
		test("test066_ok.flg");
	}

	@Test
	public void test067() {
		test("test067_ok.flg");
	}

	@Test
	public void test068() {
		test("test068_ok.flg");
	}

	@Test
	public void test069() {
		test("test069_ok.flg");
	}

	@Test
	public void test070() {
		test("test070_ok.flg");
	}

	@Test
	public void test071() {
		test("test071_ok.flg");
	}

	@Test
	public void test072() {
		test("test072_ok.flg");
	}

	@Test
	public void test073() {
		test("test073_ok.flg");
	}

	@Test
	public void test077() {
		test("test077_ok.flg");
	}

	@Test
	public void test078() {
		test("test078_ok.flg");
	}

	@Test
	public void test079() {
		test("test079_ok.flg");
	}

	@Test
	public void test081() {
		test("test081_ok.flg");
	}

	@Test
	public void test082() {
		test("test082_ok.flg");
	}

	@Test
	public void test083() {
		test("test083_ok.flg");
	}

	@Test
	public void test084() {
		test("test084_ok.flg");
	}

	@Test
	public void test085() {
		test("test085_ok.flg");
	}

	@Test
	public void test086() {
		test("test086_ok.flg");
	}

	@Test
	public void test087() {
		test("test087_ok.flg");
	}

	@Test
	public void test088() {
		test("test088_ok.flg");
	}

	@Test
	public void test089() {
		test("test089_ok.flg");
	}

	@Test
	public void test090() {
		test("test090_ok.flg");
	}

	@Test
	public void test092() {
		test("test092_ok.flg");
	}

	@Test
	public void test093() {
		test("test093_ok.flg");
	}

	@Test
	public void test094() {
		test("test094_ok.flg");
	}

	@Test
	public void test095() {
		test("test095_ok.flg");
	}

	@Test
	public void test096() {
		test("test096_ok.flg");
	}

	@Test
	public void test097() {
		test("test097_ok.flg");
	}

	@Test
	public void test099() {
		test("test099_ok.flg");
	}

	@Test
	public void test100() {
		test("test100_ok.flg");
	}

	@Test
	public void test102() {
		test("test102_ok.flg");
	}

	@Test
	public void test103() {
		test("test103_ok.flg");
	}

	@Test
	public void test104() {
		test("test104_ok.flg");
	}

	@Test
	public void test105() {
		test("test105_ok.flg");
	}

	@Test
	public void test106() {
		test("test106_ok.flg");
	}

	@Test
	public void test107() {
		test("test107_ok.flg");
	}

	@Test
	public void test108() {
		test("test108_ok.flg");
	}

	@Test
	public void test109() {
		test("test109_ok.flg");
	}

	@Test
	public void test110() {
		test("test110_ok.flg");
	}

	@Test
	public void test111() {
		test("test111_ok.flg");
	}

	@Test
	public void test112() {
		test("test112_ok.flg");
	}

	@Test
	public void test113() {
		test("test113_ok.flg");
	}

	@Test
	public void test114() {
		test("test114_ok.flg");
	}

	@Test
	public void test115() {
		test("test115_ok.flg");
	}

	@Test
	public void test116() {
		test("test116_ok.flg");
	}

	@Test
	public void test117() {
		test("test117_ok.flg");
	}

	@Test
	public void test119() {
		test("test119_ok.flg");
	}

	@Test
	public void test120() {
		test("test120_ok.flg");
	}

	@Test
	public void test121() {
		test("test121_ok.flg");
	}

	@Test
	public void test122() {
		test("test122_ok.flg");
	}

	@Test
	public void test123() {
		test("test123_ok.flg");
	}

	@Test
	public void test124() {
		test("test124_ok.flg");
	}

	@Test
	public void test125() {
		test("test125_ok.flg");
	}

	@Test
	public void test126() {
		test("test126_ok.flg");
	}

	@Test
	public void test127() {
		test("test127_ok.flg");
	}

	@Test
	public void test128() {
		test("test128_ok.flg");
	}

	@Test
	public void test129() {
		test("test129_ok.flg");
	}

	@Test
	public void test134() {
		test("test134_ok.flg");
	}

	@Test
	public void test135() {
		test("test135_ok.flg");
	}

	@Test
	public void test136() {
		test("test136_ok.flg");
	}

	@Test
	public void test137() {
		test("test137_ok.flg");
	}
	
	@Test
	public void test138() {
		test("test138_ok.flg");
	}
	
	@Test
	public void test139() {
		test("test139_ok.flg");
	}
	
	@Test
	public void test180() {
		test("test180_ok.flg");
	}
	
	@Test
	public void test181() {
		test("test181_ok.flg");
	}
	
	@Test
	public void test182() {
		test("test182_ok.flg");
	}
	
	@Test
	public void test183() {
		test("test183_ok.flg");
	}
	
	@Test
	public void test184() {
		test("test184_ok.flg");
	}

}
