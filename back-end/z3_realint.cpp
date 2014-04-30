/*
 * =====================================================================================
 * /
 * |     Filename:  z3_realint.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/07/2014 09:55:29 AM
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



#include "z3_realint.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3RealInt::Z3RealInt(){
	
}

Z3RealInt::~Z3RealInt(){
	
}

void Z3RealInt::dump_problem(string& filename_base){


	vector<string> tokens = tokenize(filename_base, ".");

	FILE* file = fopen(filename_base.c_str(), "w");
	dump_header(file);
	dump_variables(file);
	dump_extra(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);
	fclose(file);

}

void Z3RealInt::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-option :pp-decimal true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

void Z3RealInt::dump_variables(FILE* file){

	assert(free_variables.size() && "Empty free_variables");

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = z3_type(get_type(it->name));

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", position.c_str(), type.c_str());

		
	}
	

}



string Z3RealInt::canonical_representation(string in){

	return in;
}




string Z3RealInt::complement_op(string op1){

	stringstream ret;
	string content1 = content(op1);

	printf("complement_operation %s \n", op1.c_str());

	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 1)))";
	//ret << "(ite (> " << content1 << " 0) (- (+ " << content1 << " 1)) (- -256 (+ " << content1 << " 2)))";
	ret << "(- (+ " << content1 << " 1))";

	return ret.str();

}

void Z3RealInt::dump_extra(FILE* file){
	dump_type_limits(file);
}

void Z3RealInt::dump_type_limits(FILE* file){

	if(options->cmd_option_bool("unconstrained")) return;


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_sized_type(it->name);

		string position = it->position;

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (<= %s %d)))\n", position.c_str(), minval(type), position.c_str(), maxval(type) );
		
	}
}

int Z3RealInt::minval(string type){

	if(type == "Int32") return -(1 << 30);
	if(type == "Int16") return -(1 << 15);
	if(type == "Int8")  return 0;
	if(type == "Int") return   -(1 << 30);
	if(type == "Pointer") return 0;

	printf("MinVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;
}

int Z3RealInt::maxval(string type){

	if(type == "Int32") return (1 << 30);
	if(type == "Int16") return (1 << 15);
	if(type == "Int8") return 255;
	if(type == "Int") return (1 << 30);
	if(type == "Pointer") return (1 << 30);

	printf("MaxVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;

}

string Z3RealInt::internal_representation(int in, string type){
	char b[20];
	sprintf(b, "%d", in);

	//printf("internal representation in %s a %d b %s\n", in.c_str(), a, b);
	return string(b);
}

void Z3RealInt::cast_instruction(string src, string dst, string type_src, string type_dst){

	assign_instruction(src,dst);

	printf("cast_instruction_types %s %s %s %s\n", type_src.c_str(), type_dst.c_str(), z3_type(type_src).c_str(), z3_type(type_dst).c_str() );

	if( z3_type(type_src) == "Int" && z3_type(type_dst) == "Real" )
		setcontent(dst, "(to_real " + content(src) + ")" );

	if( z3_type(type_src) == "Real" && z3_type(type_dst) == "Int" )
		setcontent(dst, "(to_int " + content(src) + ")" );
	
}


map<set<pair<string, int> > , int > Z3RealInt::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

	debug && printf("\e[32m get_idx_val %s %d %d %d\e[0m\n", base.c_str(), first_address, last_address, indexes.size());
	


	set<string> index_vars = variables[base].indexes;
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[32m index \e[0m %s\n", it->c_str());

		set<string> indexes_index = variables[*it].indexes;
		for( set<string>::iterator it2 = indexes_index.begin(); it2 != indexes_index.end(); it2++ ){
			debug && printf("\e[32m index2 \e[0m %s\n", variables[*it2].name_hint.c_str() );
			index_vars.insert( variables[*it2].name_hint );
		}
	}
	
	map<set<pair<string, int> > , int > ret;

	bool is_sat;

	string idx_show;
	for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
		idx_show += *it + ",";
	}
	

	
	printf("\e[32m base \e[0m %s \e[32m idx_content \e[0m %s \e[32m indexes \e[0m %s \e[32m first_address \e[0m %d \e[32m last_address \e[0m %d\n", base.c_str(), idx_content.c_str(), idx_show.c_str(), first_address, last_address);

	int iters = 0;
	while(true){


		FILE* ftmp = fopen("/tmp/forest/idx_problem.smt2", "w");
		fprintf(ftmp, "(set-option :produce-models true)\n");
		fprintf(ftmp, "(set-logic AUFNIRA)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			fprintf(ftmp, "(declare-fun %s () Int)\n", it->c_str());
		}

		stringstream excl_expr;
		stringstream range_expr;

		//range_expr << "(and " << "(<= " << first_address << " " << idx_content << " " << last_address << ") " << "(<= " << idx_content << " " << last_address << "))";
		range_expr << "(and " << "(<= " << first_address << " " << idx_content << ") " << "(<= " << idx_content << " " << last_address << "))";


		set<set<pair<string, int> > > exclusions = get_exclusions(ret);

		//printf("exclusions.size() %d\n", exclusions.size() );

		excl_expr << "(not ";
		if(exclusions.size() > 1)
			excl_expr << "(or ";
		for( set<set<pair<string, int> > >::iterator it = exclusions.begin(); it != exclusions.end(); it++ ){
			set<pair<string, int> > fsol = (*it);
			if(fsol.size() > 1)
				excl_expr << "(and ";
			for( set<pair<string, int> >::iterator it2 = fsol.begin(); it2 != fsol.end(); it2++ ){
				excl_expr << "(= " << it2->first << " " << it2->second << ") ";
			}
			if(fsol.size() > 1)
				excl_expr << ")";
		}
		if(exclusions.size() > 1)
			excl_expr << ")";
		excl_expr << ")";



		fprintf(ftmp, "(assert %s)\n", range_expr.str().c_str());

		if(exclusions.size() > 0)
			fprintf(ftmp, "(assert %s)\n", excl_expr.str().c_str());






		fprintf(ftmp, "(check-sat)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			fprintf(ftmp, "(get-value (%s))\n", internal_condition(*it).c_str());
		}

		fprintf(ftmp, "(get-value (%s))\n", internal_condition(idx_content).c_str() );

		fclose(ftmp);

		system("z3 /tmp/forest/idx_problem.smt2 > /tmp/forest/idx_out");


		ifstream input("/tmp/forest/idx_out");
		string line;
		vector<string> result;

		while( getline( input, line ) ) {
			result.push_back(line);
		}


		if(result[0].find("error") != string::npos ){
			printf("Error in z3 execution\n");
			solve_problem();
			assert(0 && "Error in z3 execution");
		}


		is_sat = (result[0] == "sat");

		if(!is_sat){
			//printf("no sat\n");
			break;
		}

		if(iters++ == options->cmd_option_int("max_pointer_deref_combs")){
			//printf("number of iterations exceeded\n");
			break;
		}

		set<pair<string, int> > sub_sol;

		int i = 0;
		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			i++;
			string line = result[i];
			if(line.find("error") != string::npos )
				assert(0 && "Error in z3 execution");

			string varname = *it;
			string value = result_get(line);

			sub_sol.insert(pair<string, int>(varname, stoi(value)));

		}
		
		i++;
		line = result[i];
		int idx_res = stoi(result_get(line));

		//printf("idx_res %d\n", idx_res);

		ret[sub_sol] = idx_res;

		//static int p;
		//if(p++ == 3) break;

	}

	//for( set<pair<string, int> >::iterator it = sub_sol.begin(); it != sub_sol.end(); it++ ){
		//printf("sub_sol %s %d\n", it->first.c_str(), it->second);
	//}
	
	
	return ret;
	//exit(0);

}


void Z3RealInt::get_operands(string condition, string operation, string& substr, string& before, string& after, string& param1, string& param2){

		int ini = condition.find("(" + operation + " ");

		substr = close_str(condition.substr(ini));

		before = condition.substr(0, ini);
		after = condition.substr(before.length() + substr.length() );

		//param1 = parameter(substr.substr(4));
		param1 = parameter(substr.substr(2+operation.length()));
		//param2 = parameter(substr.substr(param1.length() + 5));
		param2 = parameter(substr.substr(param1.length() + 3+operation.length()));


		debug && printf("\e[32m replace_shift_constant \e[0m \e[32m ini \e[0m %d \e[32m substr \e[0m .%s. \e[32m before \e[0m .%s. \e[32m after \e[0m .%s.\n", ini, substr.c_str(), before.c_str(), after.c_str());
		debug && printf("\e[32m param1 \e[0m .%s. \e[32m param2 \e[0m .%s.\n", param1.c_str(), param2.c_str());
}

void Z3RealInt::replace_left_shift(string& condition){

	if( condition.find("<<") == string::npos ){
		return;
	} else {
		string substr, before, after, param1, param2;
		get_operands(condition, "<<", substr, before, after, param1, param2);

		if(!is_number(param2)) assert(0 && "Unsupported operation");

		int exponent = stoi(param2);
		int factor = 1 << exponent;

		condition = before + "(* " + param1 + " " + itos(factor) + ")" + after;

		//printf("condition %s\n", condition.c_str());

	}

}


void Z3RealInt::replace_right_shift(string& condition){

	if( condition.find(">>") == string::npos ){
		return;
	} else {
		string substr, before, after, param1, param2;
		get_operands(condition, ">>", substr, before, after, param1, param2);

		if(!is_number(param2)) assert(0 && "Unsupported operation");

		int exponent = stoi(param2);
		int factor = 1 << exponent;

		condition = before + "(/ " + param1 + " " + itos(factor) + ")" + after;

		//printf("condition %s\n", condition.c_str());

	}

}

void Z3RealInt::replace_and(string& condition){

	if( condition.find("(Y ") == string::npos ){
		return;
	} else {
		string substr, before, after, param1, param2;
		get_operands(condition, "Y", substr, before, after, param1, param2);

		if(!is_number(param2)) assert(0 && "Unsupported operation");


		condition = before + and_constant(param1, param2) + after;


	}
}

void Z3RealInt::replace_or(string& condition){

	if( condition.find("(O ") == string::npos ){
		return;
	} else {
		string substr, before, after, param1, param2;
		get_operands(condition, "O", substr, before, after, param1, param2);

		if(!is_number(param2)) assert(0 && "Unsupported operation");


		condition = before + or_constant(param1, param2) + after;


	}
}


string Z3RealInt::or_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = op1;

	printf("or_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << "(- " << mult1 << " " << x_bit_i_sh.str() << ")";
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + content1 + " " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}

string Z3RealInt::and_constant(string op1, string op2){

	stringstream ret;
	int op2_i = stoi(op2);
	string op2_b = binary_rep(op2_i);
	string content1 = op1;

	printf("and_constant %s %s %s %s\n", op1.c_str(),content1.c_str(), op2.c_str(), op2_b.c_str());


	vector<string> z_bits;

	for ( unsigned int i = 0,mult1=1,mult2=2; i < op2_b.length()-1; i++,mult1*=2, mult2*=2) {

		char bit = op2_b[op2_b.length()-i-1];

		printf("bit %c mult %d\n", bit, mult1);

		stringstream x_bit_i_sh;
		stringstream z_bit_i;
		stringstream z_bit_i_sh;
		x_bit_i_sh << "(- (mod " << content1 << " " << mult2 << ") (mod " << content1 << " " << mult1 << "))";

		if(bit == '1'){
			z_bit_i_sh << x_bit_i_sh.str();
		} else {
			z_bit_i_sh << "";
		}


		z_bits.push_back(z_bit_i_sh.str());
	}

	string res;

	for ( unsigned int i = 0; i < z_bits.size(); i++) {
		res += z_bits[i] + " ";
	}

	res = "(+ " + res + ")";

	//printf("\e[33m op1 \e[0m %s \e[33m op2 \e[0m %s \e[33m res \e[0m %s\n", op1.c_str(), op2.c_str(), res.c_str() );

	return res;



	return ret.str();

}


string Z3RealInt::internal_condition(string condition){

	myReplace(condition, "(% ", "(mod ");
	replace_left_shift(condition);
	replace_right_shift(condition);
	replace_and(condition);
	replace_or(condition);
	
	return condition;

}

