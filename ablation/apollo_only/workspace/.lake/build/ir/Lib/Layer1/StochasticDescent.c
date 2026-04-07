// Lean compiler output
// Module: Lib.Layer1.StochasticDescent
// Imports: public import Init public import Lib.Glue.Algebra public import Lib.Layer0.GradientFTC public import Lib.Layer0.IndepExpect public import Lib.Layer0.ConvexFOC public import Mathlib.Analysis.InnerProductSpace.Basic public import Mathlib.MeasureTheory.Integral.Bochner.Basic public import Mathlib.Probability.Independence.Basic public import Mathlib.Topology.MetricSpace.Lipschitz public import Mathlib.Data.NNReal.Defs public import Mathlib.Analysis.Calculus.Gradient.Basic public import Mathlib.Analysis.Convex.Strong
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
lean_object* initialize_sgd__apollo__ablation_Lib_Glue_Algebra(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_GradientFTC(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_IndepExpect(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_ConvexFOC(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Independence_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_MetricSpace_Lipschitz(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_NNReal_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Gradient_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Strong(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_sgd_Lib_Layer1_StochasticDescent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Glue_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Layer0_GradientFTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Layer0_IndepExpect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Layer0_ConvexFOC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Independence_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_MetricSpace_Lipschitz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_NNReal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Gradient_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Strong(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
