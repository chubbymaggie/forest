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

Options* options = new Options();
Operators* operators = new Operators();
Solver* solver = new Solver();
Database* database = new Database();
Concurrency* concurrency = new Concurrency();

void cast_instruction(char* _dst, char* _src, char* _type){
       	operators->cast_instruction(_dst, _src, _type); 
}

void NonAnnotatedCallInstr( char* _fn_name, char* _ret_to, char* _ret_type ){
	operators->NonAnnotatedCallInstr(_fn_name, _ret_to, _ret_type);
}

void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to ){
	operators->CallInstr(  _fn_name,  _oplist,  _fn_oplist,  _ret_to );
}

void select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){
	operators->select_op(_dest, _cond, _sel1, _sel2);
}

void ReturnInstr(char* _retname ){
	operators->ReturnInstr(_retname);
}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	operators->binary_op(_dst, _op1, _op2,_operation);
}

void load_instr(char* _dst, char* _addr){
	if( options->cmd_option_bool("concurrency") || options->cmd_option_bool("secuencialize"))
		concurrency->load_instr(_dst, _addr);
	else
		operators->load_instr(_dst, _addr);

}

void store_instr(char* _src, char* _addr){
	if( options->cmd_option_bool("concurrency") || options->cmd_option_bool("secuencialize"))
		concurrency->store_instr(_src, _addr);
	else
		operators->store_instr(_src, _addr);
}

void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){
	operators->cmp_instr(_dst, _cmp1, _cmp2, _type);
}

void br_instr_incond(){
	operators->br_instr_incond();
}

void begin_bb(char* name){
	operators->begin_bb(name);
}

void end_bb(char* name){
	operators->end_bb(name);
}

void global_var_init(char* _varname, char* _type, char* _values){
	operators->global_var_init(_varname, _type,_values);
}

void alloca_instr(char* _reg, char* _subtype){
	operators->alloca_instr(_reg, _subtype);
}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){
	operators->getelementptr(_dst, _pointer, _indexes,_offset_tree);
}

void begin_sim(){
	operators->begin_sim();
}

void BeginFn(char* _fn_name){
	operators->BeginFn(_fn_name);
}

void end_sim(){
	operators->end_sim();
}

bool br_instr_cond(char* _cmp, char* _joints){
	return operators->br_instr_cond(_cmp, _joints);
}


void mutex_lock(char* _mutex_name, char* _sync_name){
	if(options->cmd_option_bool("concurrency"))
		concurrency->mutex_lock_info(_mutex_name, _sync_name);
	if(options->cmd_option_bool("secuencialize"))
		concurrency->mutex_lock_constraints(_mutex_name, _sync_name);
}

void mutex_unlock(char* _mutex_name, char* _sync_name){
	if(options->cmd_option_bool("concurrency"))
		concurrency->mutex_unlock_info(_mutex_name, _sync_name);
	if(options->cmd_option_bool("secuencialize"))
		concurrency->mutex_unlock_constraints(_mutex_name, _sync_name);
}

void begin_concurrency(){
	concurrency->begin_concurrency();
}

void end_concurrency(){
	concurrency->end_concurrency();
}



