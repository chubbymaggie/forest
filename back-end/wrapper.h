/*
 * =====================================================================================
 * /
 * |     Filename:  wrapper.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/14/2013 03:25:31 AM
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

#ifndef _WRAPPER_H_
#define _WRAPPER_H_

#include "options.h"
#include "operators.h"
#include "solver.h"
#include "operators.h"
#include "concurrency.h"

/**
 * @brief Called when a binary operation is performed among two variables
 *
 * @param dst: Destination name
 * @param op1: First operand name
 * @param op2: Second operand name
 * @param operation: Operation kind
 */
extern "C" void binary_op(char*, char*, char*, char*);

/**
 * @brief Called when a cast instruction is performed
 *
 * @param _dst: Name of the destination register
 * @param _src: Name of the source register
 * @param type: Type of the destination data
 *
 * @return 
 */
extern "C" void cast_instruction(char*, char*, char*);

/**
 * @brief Called when a load instruction assigns the value of a memory position (pointed by the register named addr) to a register
 *
 * @param _dst: name of the destination register
 * @param _addr: name of the register that contains the address
 */
extern "C" void load_instr(char*, char*);

/**
 * @brief Called when a store instruction assigns the value of a register to a memory position
 *
 * @param _src: register name
 * @param _addr: name of the register that contains the address of the store
 */
extern "C" void store_instr(char*, char*);

/**
 * @brief Comparison instruction
 *
 * @param _dst: name of the destination
 * @param _cmp1: Name of the first register
 * @param _cmp2: Name of the second register
 * @param _type: Type of comparison
 */
extern "C" void cmp_instr(char*, char*, char*, char*);

/**
 * @brief Conditional branch instruction
 *
 * @param _cmp: Name of the register that contains the branch condition
 *
 * @return 
 */
extern "C" bool br_instr_cond(char*, char*);

/**
 * @brief Inconditional branch instruction
 */
extern "C" void br_instr_incond();

/**
 * @brief  Begin basic Block
 *
 * @param name: Name of the basic block
 */
extern "C" void begin_bb(char* a);

/**
 * @brief End basic block
 *
 * @param name
 */
extern "C" void end_bb(char* a);

/**
 * @brief Function that is called when a new variable is allocated
 *
 * @param _reg: name of the register that holds the position of new variable in memory
 * @param _type: Data type of allocated value
 */
extern "C" void alloca_instr(char* a, char* b);

/**
 * @brief Function that is called at the begining of simulation
 */
extern "C" void begin_sim();

/**
 * @brief Function that is called at the end of simulation
 */
extern "C" void end_sim();

/**
 * @brief Called when a getelementptr operation is performed
 *
 * @param _dst: Destination register with the calculated offset
 * @param _pointer: Source pointer
 * @param _indexes: Indexes with the values to be accessed
 * @param _offset_tree: Tree containing the offset of each index
 */
extern "C" void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree);


/**
 * @brief Called to initialize a global variable
 *
 * @param _name: Name of the global variable
 * @param _type: Type
 * @param _value: Values to be initialized
 */
extern "C" void global_var_init(char* _name,char* _type, char* _value);


/**
 * @brief Function to instrument a functin call
 *
 * @param _fn_name: Name of the called function
 * @param _oplist: Actual parameters
 * @param _fn_oplist: Formal parameters
 * @param _ret_to
 */
extern "C" void CallInstr( char* _fn_name, char* _oplist, char* _fn_oplist, char* _ret_to );
extern "C" void Free_fn( char* _fn_name );

extern "C" void NonAnnotatedCallInstr( char* _fn_name, char* _ret_to, char* _ret_type );

extern "C" void ReturnInstr(char* _retname );
extern "C" void BeginFn(char* _fn_name);

extern "C" void select_op(char* dest, char* cond, char* sel1, char* sel2 );

extern "C" void mutex_lock(char* _mutex_name, char* _sync_name);
extern "C" void mutex_unlock(char* _mutex_name, char* _sync_name);
extern "C" void begin_concurrency();
extern "C" void end_concurrency();

#endif /* end of include guard: _WRAPPER_H_ */
