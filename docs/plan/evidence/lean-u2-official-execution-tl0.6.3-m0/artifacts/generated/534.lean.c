// Lean compiler output
// Module: «534»
// Imports: public import Init public meta import Init
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_foo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_foo___closed__0 = (const lean_object*)&l_foo___closed__0_value;
LEAN_EXPORT lean_object* l_foo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hi"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* l_main___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___y_6_; uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = lean_unsigned_to_nat(5u);
v___x_13_ = lean_nat_dec_eq(v___x_11_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_inc(v___x_11_);
v___x_14_ = lean_array_push(v_b_4_, v___x_11_);
v___y_6_ = v___x_14_;
goto v___jp_5_;
}
else
{
v___y_6_ = v_b_4_;
goto v___jp_5_;
}
}
else
{
return v_b_4_;
}
v___jp_5_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0___boxed(lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_, lean_object* v_b_18_){
_start:
{
size_t v_i_boxed_19_; size_t v_stop_boxed_20_; lean_object* v_res_21_; 
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_20_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_as_15_, v_i_boxed_19_, v_stop_boxed_20_, v_b_18_);
lean_dec_ref(v_as_15_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_foo(lean_object* v_array_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_zero_26_; uint8_t v_isZero_27_; 
v_zero_26_ = lean_unsigned_to_nat(0u);
v_isZero_27_ = lean_nat_dec_eq(v_x_25_, v_zero_26_);
if (v_isZero_27_ == 1)
{
lean_dec(v_x_25_);
lean_dec_ref(v_array_24_);
return v_zero_26_;
}
else
{
lean_object* v_one_28_; lean_object* v_n_29_; lean_object* v___y_31_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_one_28_ = lean_unsigned_to_nat(1u);
v_n_29_ = lean_nat_sub(v_x_25_, v_one_28_);
lean_dec(v_x_25_);
v___x_39_ = lean_array_get_size(v_array_24_);
v___x_40_ = ((lean_object*)(l_foo___closed__0));
v___x_41_ = lean_nat_dec_lt(v_zero_26_, v___x_39_);
if (v___x_41_ == 0)
{
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_40_;
goto v___jp_30_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = lean_nat_dec_le(v___x_39_, v___x_39_);
if (v___x_42_ == 0)
{
if (v___x_41_ == 0)
{
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_40_;
goto v___jp_30_;
}
else
{
size_t v___x_43_; size_t v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((size_t)0ULL);
v___x_44_ = lean_usize_of_nat(v___x_39_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_array_24_, v___x_43_, v___x_44_, v___x_40_);
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_45_;
goto v___jp_30_;
}
}
else
{
size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((size_t)0ULL);
v___x_47_ = lean_usize_of_nat(v___x_39_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_array_24_, v___x_46_, v___x_47_, v___x_40_);
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_48_;
goto v___jp_30_;
}
}
v___jp_30_:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v___y_31_);
v___x_33_ = lean_nat_dec_eq(v___x_32_, v_zero_26_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_arrayOfLast_37_; 
v___x_34_ = lean_nat_sub(v___x_32_, v_one_28_);
v___x_35_ = lean_array_get(v_zero_26_, v___y_31_, v___x_34_);
lean_dec(v___x_34_);
lean_dec_ref(v___y_31_);
v___x_36_ = lean_mk_empty_array_with_capacity(v_one_28_);
v_arrayOfLast_37_ = lean_array_push(v___x_36_, v___x_35_);
v_array_24_ = v_arrayOfLast_37_;
v_x_25_ = v_n_29_;
goto _start;
}
else
{
lean_dec_ref(v___y_31_);
lean_dec(v_n_29_);
return v_zero_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object* v_s_49_){
_start:
{
lean_object* v___x_51_; lean_object* v_putStr_52_; lean_object* v___x_53_; 
v___x_51_ = lean_get_stdout();
v_putStr_52_ = lean_ctor_get(v___x_51_, 4);
lean_inc_ref(v_putStr_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_apply_2(v_putStr_52_, v_s_49_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object* v_s_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__0(lean_object* v_s_57_){
_start:
{
uint32_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = 10;
v___x_60_ = lean_string_push(v_s_57_, v___x_59_);
v___x_61_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__0___boxed(lean_object* v_s_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_IO_println___at___00main_spec__0(v_s_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* _lean_main(){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_main___closed__0));
v___x_68_ = l_IO_println___at___00main_spec__0(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = _lean_main();
return v_res_70_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_00534(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize_runtime_module();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    return _lean_main();
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  res = initialize_00534(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
