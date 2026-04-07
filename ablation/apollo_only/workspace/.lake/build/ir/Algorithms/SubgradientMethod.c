// Lean compiler output
// Module: Algorithms.SubgradientMethod
// Imports: public import Init public import Main public import Lib.Glue.Algebra public import Lib.Glue.Probability public import Lib.Layer0.IndepExpect
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
lean_object* initialize_sgd_Main(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Glue_Algebra(uint8_t builtin);
lean_object* initialize_sgd_Lib_Glue_Probability(uint8_t builtin);
lean_object* initialize_sgd__apollo__ablation_Lib_Layer0_IndepExpect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_sgd_Algorithms_SubgradientMethod(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Glue_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd_Lib_Glue_Probability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_sgd__apollo__ablation_Lib_Layer0_IndepExpect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
