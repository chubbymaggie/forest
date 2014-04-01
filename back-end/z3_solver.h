/*
 * =====================================================================================
 * /
 * |     Filename:  solver.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:46 PM
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


#ifndef _SOLVER_H_
#define _SOLVER_H_

#include "solver_wrapper.h"


class Z3Solver : public SolverWrapper {
public:
	Z3Solver ();
	virtual ~Z3Solver ();

protected:
	
};

#endif /* end of include guard: _SOLVER_H_ */
