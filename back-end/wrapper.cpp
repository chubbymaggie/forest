/*
 * =====================================================================================
 * /
 * |     Filename:  wrapper.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/14/2013 03:25:05 AM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include "wrapper.h"
#include "options.h"
#include "operators.h"
#include "solver_wrapper.h"
#include "operators.h"
#include "measurement.h"
#include "timer.h"
#include "z3_solver.h"
#include "z3_bitvector.h"
#include "database.h"

Options* options = new Options();
Operators* operators = new Operators();
SolverWrapper* solver = new Z3BitVector();
Database* database = new Database();
Measurement* measurement = new Measurement();
Timer* timer = new Timer();

void cast_instruction(char* _dst, char* _src, char* _type){
	timer->start_timer();
       	operators->cast_instruction(_dst, _src, _type); 
	timer->end_timer("cast_instruction");
}

void NonAnnotatedCallInstr( char* _fn_name, char* _ret_type ){
	timer->start_timer();
	operators->NonAnnotatedCallInstr(_fn_name, _ret_type);
	timer->end_timer("NonAnnotatedCallInstr");
}

void CallInstr_post( char* _fn_name, char* _ret_type ){
	timer->start_timer();
	operators->CallInstr_post( _fn_name, _ret_type );
	timer->end_timer("CallInstr_post");
}

void CallInstr( char* _oplist, char* _ret_to ){
	timer->start_timer();
	operators->CallInstr( _oplist,  _ret_to );
	timer->end_timer("CallInstr");
}

void select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){
	timer->start_timer();
	operators->select_op(_dest, _cond, _sel1, _sel2);
	timer->end_timer("select_op");
}

void ReturnInstr(char* _retname ){
	timer->start_timer();
	operators->ReturnInstr(_retname);
	timer->end_timer("ReturnInstr");
}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	timer->start_timer();
	operators->binary_op(_dst, _op1, _op2,_operation);
	timer->end_timer("binary_op");
}

void load_instr(char* _dst, char* _addr){
	timer->start_timer();
	operators->load_instr(_dst, _addr);
	timer->end_timer("load_instr");

}

void store_instr(char* _src, char* _addr){
	timer->start_timer();
	operators->store_instr(_src, _addr);
	timer->end_timer("store_instr");
}

void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){
	timer->start_timer();
	operators->cmp_instr(_dst, _cmp1, _cmp2, _type);
	timer->end_timer("cmp_instr");
}

void br_instr_incond(){
	timer->start_timer();
	operators->br_instr_incond();
	timer->end_timer("br_instr_incond");
}

void begin_bb(char* name){
	if(options->cmd_option_bool("measurement")){
		measurement->begin_bb(name);
	} else {
		timer->start_timer();
		operators->begin_bb(name);
		timer->end_timer("begin_bb");
	}
}

void end_bb(char* name){
	timer->start_timer();
	if(options->cmd_option_bool("measurement"))
		measurement->end_bb(name);
	else
		operators->end_bb(name);
	timer->end_timer("end_bb");
}

void global_var_init(char* _varname, char* _type, char* _values){
	timer->start_timer();
	operators->global_var_init(_varname, _type,_values);
	timer->end_timer("global_var_init");
}

void alloca_instr(char* _reg, char* _subtype){
	timer->start_timer();
	operators->alloca_instr(_reg, _subtype);
	timer->end_timer("alloca_instr");
}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){
	timer->start_timer();
	operators->getelementptr(_dst, _pointer, _indexes,_offset_tree);
	timer->end_timer("getelementptr");
}

void begin_sim_measurement(char* functions, char* bbs){
	timer->start_timer();
	measurement->begin_sim_measurement(functions, bbs);
	timer->end_timer("begin_sim_measurement");
}

void begin_sim(){
	timer->start_timer();
	operators->begin_sim();
	timer->end_timer("begin_sim");
}

void BeginFn(char* _fn_name, char* _fn_oplist ){
	timer->start_timer();

	if(options->cmd_option_bool("measurement"))
		measurement->BeginFn(_fn_name);
	else
		operators->BeginFn(_fn_name, _fn_oplist);
	timer->end_timer("BeginFn");
}

void EndFn(){
	measurement->EndFn();
}

void end_sim(){
	if(options->cmd_option_bool("measurement"))
		measurement->end_sim();
	else
		operators->end_sim();

	timer->print_times();
}

bool br_instr_cond(char* _cmp, char* _joints){
	//timer->start_timer();
	bool ret = operators->br_instr_cond(_cmp, _joints);
	//timer->end_timer("br_instr_cond");

	return ret;
}

void br_instr_cond_measurement(bool value){
	measurement->br_instr_cond_measurement(value);
}

void Free_fn( char* _oplist ){
	timer->start_timer();

	operators->Free_fn(_oplist);
	timer->end_timer("Free_fn");
}

short vector_short(char* _name){

	return measurement->vector_short(_name);
}

int vector_int(char* _name){
	return measurement->vector_int(_name);
}

char vector_char(char* _name){
	return measurement->vector_char(_name);
}

void pivot_variable(char* a){

	operators->pivot_variable(a);

}

void pivot_hint(char* a){
	operators->pivot_hint(a);
}

void pointer_ranges(){
	operators->pointer_ranges();
}

void Memcpy(char* a, char* b, char* c, char* d, char* e){
	timer->start_timer();
	operators->memcpy(a,b,c,d,e);
	timer->end_timer("Memcpy");
}

