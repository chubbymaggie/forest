/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:31 PM
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

#include "z3_solver.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"

#define check_mangled_name(A) operators->check_mangled_name(A)

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3Solver::Z3Solver(){
	
}

Z3Solver::~Z3Solver(){
	
}

void Z3Solver::solve_problem(){

	if(options->cmd_option_str("max_depth") != "" && conditions.size()-1 > options->cmd_option_int("max_depth")){
		sat = 0;
		return;
	}

	timer->start_timer();

	vector<string> ret_vector;

	sat = 0;

	//printf("call to get_problem_num\n");
	string filename;

	if(options->cmd_option_bool("sequential_problems")){
		int n = database->get_problem_num();
		filename = "z3_" + itos(n) + ".smt2";
	} else {
		filename = "z3_" + itos(rand()) + ".smt2";
	}

	options->read_options();

	timer->start_timer();

	dump_problem(filename);

	timer->end_timer("dump");
	debug && printf("\e[31m filename solve problem \e[0m %s\n", filename.c_str() );

	if(options->cmd_option_bool("see_each_problem"))
		getchar();



	FILE *fp;
	stringstream command;

	command << "z3 " << filename;
	command << " > /tmp/z3_output";


struct timespec ping_time;
struct timespec pong_time;
clock_gettime(CLOCK_MONOTONIC, &ping_time);


	system(command.str().c_str());

clock_gettime(CLOCK_MONOTONIC, &pong_time);
spent_time = 0;
spent_time += pong_time.tv_sec - ping_time.tv_sec;
spent_time *= 1e9;
spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
spent_time /= 1e6;




	ifstream input("/tmp/z3_output");
	string line;
	
	while( getline( input, line ) ) {
		ret_vector.push_back(line);
	}
	
	string         sat_str       = ret_vector[0];

	if(sat_str.find("error") != string::npos ){
		printf("error_in_z3\n");
		assert(0 && "Error in z3 execution");
	}
	if(sat_str.find("unknown") != string::npos )
		printf("Warning: unknown sat\n");

	sat = get_is_sat(sat_str);

	debug && printf("\e[31m problem solved \e[0m\n" );

	if(!sat){
		timer->end_timer("solver");
		return;
	}


	bool sat = 0;


	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	set<NameAndPosition> free_variables_aux;

	timer->start_timer();
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string varname = it->name;
		string value = canonical_representation(result_get(*it_ret));
		string hint = it->position;


		debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
		//it->value = value;
		//set_real_value_hint(hint, value);
		//variables[varname].real_value = value;

	}

	free_variables = free_variables_aux;


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string name = it->first;
		string value = canonical_representation(result_get(*it_ret));


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}


	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, canonical_representation(result_get(*it_ret)));

		it_ret++;
	}
	timer->end_timer("get_values");

	timer->end_timer("solver");
}

void Z3Solver::dump_conditions(FILE* file){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n",it->cond.c_str() );
	}
	
}

void Z3Solver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void Z3Solver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		//printf("----- name %s type %s\n", it->first.c_str(), gettype(it->first).c_str() );

		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->second.content).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	
	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", internal_condition(it->second).c_str(), it->first.c_str());
	}
	
	
	
}

void Z3Solver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}

void Z3Solver::binary_instruction(string dst, string op1, string op2, string operation){

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(op1)) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(op2)) assert(0 && "Wrong op2 for binary_instruction");
	if(!implemented_operation(operation)) assert(0 && "Not implemented operation");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s (%s %s)\e[0m\n",
			dst.c_str(),op1.c_str(), operation.c_str(),op2.c_str(),
		        get_type(op1).c_str(), get_type(op2).c_str() );


	stringstream content_ss;



	if( variables[op1].type != "" )
		settype(dst, get_type(op1));
	else
		settype(dst, get_type(op2));




	if( operation == "#" ){ // neq_operation
		neq_operation(op1, op2, dst, content_ss);
	} else if (operation == "%") { // rem_operator
		rem_operator(op1, op2, dst, content_ss);
	} else if (operation == "R" ) { // right_shift
		right_shift(op1, op2, dst, content_ss);
	} else if (operation == "L" ) { // left_shift
		left_shift(op1, op2, dst, content_ss);
	} else if (operation == "Y" ) { // and_operation
		and_operation(op1, op2, dst, content_ss);
	} else if (operation == "O" ) { // or_operation
		or_operation(op1, op2, dst, content_ss);
	} else if (operation == "X" ) { // xor_operation
		xor_operation(op1, op2, dst, content_ss);
	} else if(operation == "<="){ // leq_operation
		leq_operation(op1, op2, dst, content_ss);
	} else if(operation == "u<="){ // uleq_operation
		uleq_operation(op1, op2, dst, content_ss);
	} else if(operation == ">="){ // geq_operation
		geq_operation(op1, op2, dst, content_ss);
	} else if(operation == "<"){ // lt_operation
		lt_operation(op1, op2, dst, content_ss);
	} else if(operation == ">"){ // bt_operation
		bt_operation(op1, op2, dst, content_ss);
	} else if(operation == "="){ // eq_operation
		eq_operation(op1, op2, dst, content_ss);
	} else if(operation == "+"){ // add_operation
		add_operation(op1, op2, dst, content_ss);
	} else if(operation == "-"){ // sub_operation
		sub_operation(op1, op2, dst, content_ss);
	} else if(operation == "*"){ // mul_operation
		mul_operation(op1, op2, dst, content_ss);
	} else if(operation == "/"){ // div_operation
		div_operation(op1, op2, dst, content_ss);
	}

	variables[dst].content = content_ss.str();

	propagate_binary(op1, op2, dst);

	if( variables[op1].type != "" ) variables[dst].type = variables[op1].type;
	if( variables[op2].type != "" ) variables[dst].type = variables[op2].type;



	if( variables[op1].type == "bool" && op2 == "constant_0" && operation == "<" ){
		debug && printf("\e[32m Propagation of bool constraint \e[0m\n");

		content_ss.str("");
		content_ss << content(op1);
		variables[dst].content = "false";

		set_real_value(dst, "false" );
	}


	if( variables[op1].type == "Int" && variables[op2].type == "bool" && operation == "+" ){
		debug && printf("\e[32m Propagation of bool constraint \e[0m\n");

		content_ss.str("");
		content_ss << content(op1);
		variables[dst].content = "(+ " + content(op1) + " " + "(ite " + content(op2) + " 1 0)" + ")";

		if( realvalue(op2) == "true" )
			set_real_value(dst, internal_representation(stoi(realvalue(op1)) + 1, "IntegerTyID8") );
		else if( realvalue(op2) == "false" )
			set_real_value(dst, internal_representation(stoi(realvalue(op1)) + 0, "IntegerTyID8") );
		else
			assert(0 && "Invalid boolean value");
	}



	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d \e[32m last_address\e[0m  %d %d \e[32m firstaddress \e[0m %d %d\n",
                 variables[dst ].content.c_str(), variables[dst].type.c_str(), realvalue(dst).c_str(),
		get_is_propagated_constant(dst),
		get_last_address(op1), get_last_address(dst), get_first_address(op1), get_first_address(dst) );


}




void Z3Solver::right_shift(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(>> " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) >> places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

void Z3Solver::left_shift(string op1, string op2, string dst, stringstream& content_ss){



		content_ss << "(<< " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) << places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());


}

void Z3Solver::and_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(Y " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) & stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

void Z3Solver::or_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(O " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) | stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

void Z3Solver::assign_instruction(string src, string dst, string fn_name){

	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n",dst.c_str(),src.c_str() );

	if(!check_mangled_name(src)) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for assign");



		bool forcedfree = is_forced_free(src);
		if(forcedfree){

			string cntnt = variables[src].content;
			debug && printf("\e[36m Source is forced_free %s %s\e[0m\n",src.c_str(), cntnt.c_str());
			setcontent(src, "");
		}
		variables[dst].content = content(src);

		if(forcedfree){
			set_first_content(src, variables[dst].content);
			printf("variables[dst].content %s\n", variables[dst].content.c_str() );

		}


	propagate_unary(src, dst, forcedfree);

	//if( variables[dst].type == "" ) assert(0 && "No type in dst");
	string prev_type = variables[dst].type;
	string new_type = get_type(src);

	settype(dst, gettype(src));

	if(is_constant(src) && prev_type != new_type && prev_type != "Pointer" && prev_type != ""){
		printf("Types %s %s\n", prev_type.c_str(), new_type.c_str());
		settype(dst, prev_type);
	}

	if(variables[dst].type == "")
		settype(dst, prev_type);

	//printf("set_real_value inside assign %s %s %s\n", dst.c_str(), src.c_str(), realvalue(src).c_str() );
	set_real_value( dst, realvalue(src) );



	//debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[dst].content.c_str(), variables[dst].type.c_str() );
	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s %s %s\e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d %d \e[32m lastaddress\e[0m  %d %d \e[32m \e[32m firstaddress \e[0m \e[0m %d %d\n",
                 variables[dst].content.c_str(),
		 variables[src].type.c_str(), variables[dst].type.c_str(), prev_type.c_str(),
		 realvalue(dst).c_str(), get_is_propagated_constant(src), get_is_propagated_constant(dst),
		 get_last_address(src), get_last_address(dst), get_first_address(src), get_first_address(dst) );




}

string Z3Solver::z3_type(string type){
	if(type == "Pointer")
		return "Int";
	if(type == "FloatTyID")
		return "Real";
	if(type == "IntegerTyID32")
		return "Int";

	return type;
}


bool Z3Solver::need_for_dump(string name, string content){
		if( content == "" ) return false;
		if( gettype(name) == "Function") return false;
		if( get_is_propagated_constant(name) ) return false;
		return true;
}

void Z3Solver::neq_operation(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(not (= " << content(op1 ) << " " <<  content(op2 ) << "))";

		if(get_type(op1) == "bool" && op2 == "constant_0"){
			content_ss.str("");
			content_ss << "(not (= " << content(op1) << " " << "false" << "))";
		}

		//fflush(stdout); fflush(stderr);
		//printf("realvalue_op1 %s realvalue_op2 %s\n", realvalue(op1).c_str(), realvalue(op2).c_str() );

		string value_1_s = realvalue(op1);
		string value_2_s = realvalue(op2);
		int value_1;
		int value_2;

		if(value_1_s == "true"){
			value_1 = 1;
		} else if(value_1_s == "false"){
			value_1 = 0;
		} else {
			value_1 = stoi(value_1_s);
		}

		if(value_2_s == "true"){
			value_2 = 1;
		} else if(value_2_s == "false"){
			value_2 = 0;
		} else {
			value_2 = stoi(value_2_s);
		}

		set_real_value(dst, ( value_1 != value_2 )?"true":"false" );
}

void Z3Solver::rem_operator(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(% " << content(op1 ) << " " <<  content(op2 ) << ")";

		stringstream result; result << stoi(realvalue(op1)) % stoi(realvalue(op2));
		set_real_value(dst, result.str());

}




void Z3Solver::leq_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(<= " << content(op1 ) << " " <<  content(op2 ) << ")";
		set_real_value(dst, ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false" );
}

void Z3Solver::uleq_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(<= " <<
			"(ite " << "(< " << content(op1) << " 0)" << "(+ 4294967296 " << content(op1) << ") " << content(op1) << ") " <<
			"(ite " << "(< " << content(op2) << " 0)" << "(+ 4294967296 " << content(op2) << ") " << content(op2) << ") " <<
			")";


		set_real_value(dst, ( (unsigned int)stoi(realvalue(op1) ) <= (unsigned int)stoi( realvalue(op2) ) )?"true":"false" );
}

void Z3Solver::geq_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(>= " << content(op1 ) << " " <<  content(op2 ) << ")";
		set_real_value(dst, ( stoi(realvalue(op1) ) >= stoi( realvalue(op2) ) )?"true":"false" );
}

void Z3Solver::lt_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(< " << content(op1 ) << " " <<  content(op2 ) << ")";
		set_real_value(dst, ( stoi(realvalue(op1) ) < stoi( realvalue(op2) ) )?"true":"false" );
}

void Z3Solver::bt_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(> " << content(op1 ) << " " <<  content(op2 ) << ")";
		set_real_value(dst, ( stoi(realvalue(op1) ) > stoi( realvalue(op2) ) )?"true":"false" );
}

void Z3Solver::eq_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(= " << content(op1 ) << " " <<  content(op2 ) << ")";
		set_real_value(dst, (stoi(realvalue(op1)) == stoi(realvalue(op2)))?"true":"false" );
}

void Z3Solver::add_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(+ " << content(op1 ) << " " <<  content(op2 ) << ")";

		stringstream result;
		if( get_type(dst) == "Real" ){
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else if (get_type(dst) == "Int") {
			result << stoi(realvalue(op1)) + stoi(realvalue(op2)), gettype(op1);
		} else if( get_type(dst) == "Pointer" ) {
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else {
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
}


void Z3Solver::xor_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(X " << content(op1 ) << " " <<  content(op2 ) << ")";

		stringstream result;
		if( get_type(dst) == "Real" ){
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else if (get_type(dst) == "Int") {
			result << stoi(realvalue(op1)) + stoi(realvalue(op2)), gettype(op1);
		} else if( get_type(dst) == "Pointer" ) {
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else {
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
}



void Z3Solver::sub_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(- " << content(op1 ) << " " <<  content(op2 ) << ")";


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) - stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
}


void Z3Solver::mul_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(* " << content(op1 ) << " " <<  content(op2 ) << ")";

		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) * stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) * stoi(realvalue(op2)), gettype(op1);
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
}

void Z3Solver::div_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(/ " << content(op1 ) << " " <<  content(op2 ) << ")";


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) / stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) / stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");

		set_real_value(dst, result.str());
}


string Z3Solver::internal_representation(int a, string type){
	return itos(a);
}




