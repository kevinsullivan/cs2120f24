-- This module serves as the root of the `Cs2120f24` library.
-- Import modules here that should be built as part of the library.

/-
LECTURE FILES
-/

-- propositional logic, lecture
import «Cs2120f24».Lectures.«02_prop_logic».formal.utilities
import «Cs2120f24».Lectures.«02_prop_logic».formal.domain
import «Cs2120f24».Lectures.«02_prop_logic».formal.syntax
import «Cs2120f24».Lectures.«02_prop_logic».formal.interpretation
import «Cs2120f24».Lectures.«02_prop_logic».formal.semantics
import «Cs2120f24».Lectures.«02_prop_logic».formal.Main


-- natural number arithmetic, lecture
import «Cs2120f24».Lectures.«02_prop_logic».formal.model_theory.properties
import «Cs2120f24».Lectures.«02_prop_logic».formal.model_theory.models
import «Cs2120f24».Lectures.«02_prop_logic».formal.model_theory.counterexamples

/-
LIBRARY FILES
-/

-- Propositional logic
import «Cs2120f24».Library.propLogic.domain
import «Cs2120f24».Library.propLogic.syntax
import «Cs2120f24».Library.propLogic.semantics
import «Cs2120f24».Library.propLogic.interpretation
import «Cs2120f24».Library.propLogic.utilities

-- Propositional logic model theory
import «Cs2120f24».Library.propLogic.model_theory.truth_table
import «Cs2120f24».Library.propLogic.model_theory.properties
import «Cs2120f24».Library.propLogic.model_theory.models
import «Cs2120f24».Library.propLogic.model_theory.counterexamples

-- Natural number arithmetic
import «Cs2120f24».Library.natArithmetic.syntax
import «Cs2120f24».Library.natArithmetic.domain
import «Cs2120f24».Library.natArithmetic.semantics

-- Propositional with natural number arithmetic
import «Cs2120f24».Library.propLogicWithArith.syntax
import «Cs2120f24».Library.propLogicWithArith.domain
import «Cs2120f24».Library.propLogicWithArith.semantics
