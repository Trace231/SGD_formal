// Lean compiler output
// Module: Lib.Layer0.ConvexFOC
// Imports: public import Init public import Lib.Layer0.GradientFTC public import Mathlib.Analysis.Convex.Deriv public import Mathlib.Analysis.Convex.Strong public import Mathlib.LinearAlgebra.AffineSpace.AffineMap public import Mathlib.Analysis.InnerProductSpace.Calculus
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_GradientFTC(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Deriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Strong(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_AffineSpace_AffineMap(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Calculus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_ConvexFOC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Layer0_GradientFTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Deriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Strong(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_AffineSpace_AffineMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Calculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
