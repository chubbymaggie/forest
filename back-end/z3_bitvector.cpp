/*
 * =====================================================================================
 * /
 * |     Filename:  z3_bitvector.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/02/2014 09:30:47 AM
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


#include "z3_bitvector.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"
#include "architecture.cpp"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3BitVector::Z3BitVector(){
	
}

Z3BitVector::~Z3BitVector(){
	
}


void Z3BitVector::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");

}

void Z3BitVector::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);
		int bits;

		//printf("dump_variables_type %s\n", type.c_str());

		if(type == "IntegerTyID32")
			bits = 32;
		else if(type == "IntegerTyID16")
			bits = 16;
		else if(type == "IntegerTyID8")
			bits = 8;
		else
			assert(0 && "Unknown Type");

		//dump_variable(position, type, file);
		fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);

		
	}
	

}

void Z3BitVector::right_shift(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(bvlshr " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) >> places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

void Z3BitVector::left_shift(string op1, string op2, string dst, stringstream& content_ss){



		content_ss << "(bvshl " << content(op1) << " " << content(op2) << ")";

		int places = stoi( realvalue(op2) );

		int result_i = stoi(realvalue(op1)) << places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());


}

void Z3BitVector::and_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvand " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) & stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

void Z3BitVector::or_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvor " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) | stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}

string Z3BitVector::canonical_representation(string in){

	// printf("canonical_representation in %s\n", in.c_str() ); fflush(stdout);
	if(in[0] != '#' && in != "true" && in != "false")
		assert(0 && "Canonical_Representation of a non-internal");


	if(in == "false") return "false";
	if(in == "true") return "true";

	int a;
	char ret_str[10];
	sscanf(in.substr(2).c_str(), "%x", &a);
	sprintf(ret_str, "%d", a);

	//printf("canonical_representation in %s a %d ret %s\n", in.c_str(), a, ret_str );

	return string(ret_str);
}

string Z3BitVector::internal_representation(int in, string type){
	return hex_representation(in, type);
}

string Z3BitVector::name_operation(string operation){
	if(operation == "*") return "bvmul";
	if(operation == "+") return "bvadd";
	if(operation == "-") return "bvsub";
	if(operation == "/") return "bvdiv";
	if(operation == "%") return "bvmod";
	if(operation == "<=") return "bvsle";
	if(operation == ">=") return "bvsge";
	if(operation == ">") return "bvsgt";
	if(operation == "<") return "bvslt";

	assert(0 && "Unknown operation");
}


void Z3BitVector::xor_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(bvxor " << content(op1) << " " << content(op2) << ")";

		int result_i = stoi(realvalue(op1)) && stoi(realvalue(op2));

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

}



void Z3BitVector::dump_extra(FILE* file){
}


string concat_begin(int size_bits, int num){
	printf("bits %d\n", size_bits);
	char ret[30];
	if(size_bits ==  8) sprintf(ret, "#x%02x", num);
	else if(size_bits == 16) sprintf(ret, "#x%04x", num);
	else if(size_bits == 24) sprintf(ret, "#x%06x", num);
	else if(size_bits == 32) sprintf(ret, "#x%08x", num);
	else assert(0 && "Unknown number of bits");
	return string(ret);
}

void Z3BitVector::cast_instruction(string src, string dst, string type_src, string type_dst){

	debug && printf("\e[32m cast_instruction %s %s %s %s\e[0m\n", src.c_str(), dst.c_str(), type_src.c_str(), type_dst.c_str() );

	int bits_src = bits(type_src);
	int bits_dst = bits(type_dst);
	int diff = bits_dst - bits_src;

	assign_instruction(src,dst);
	settype(dst, type_dst);

	if( diff > 0 ){
		string concat_start = concat_begin(bits_dst - bits_src, 0);
		string content_dst = "(concat " + concat_start + " " + content(src) + ")";
		setcontent(dst, content_dst);
		printf("dst_content %s\n", content(dst).c_str());
	}

	if( diff < 0 ){
		string content_dst = "((_ extract " + itos(bits(type_dst)-1) + " 0) " + content(src) + ")";
		setcontent(dst, content_dst);
		printf("dst_content %s\n", content(dst).c_str());
	}
	
}


map<set<pair<string, int> > , int > Z3BitVector::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

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

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			string type = gettype("mem_" + realvalue(find_by_name_hint(*it)));
			fprintf(ftmp, "(declare-const %s (_ BitVec %d))\n", it->c_str(), bits(type)  );
		}

		stringstream excl_expr;
		stringstream range_expr;

		range_expr << "(and " << "(bvsle " << internal_representation(first_address, "PointerTyID") << " " << idx_content << ") " << "(bvsle " << idx_content << " " << internal_representation(last_address, "PointerTyID") << "))";


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
				excl_expr << "(= " << it2->first << " " << internal_representation(it2->second, gettype("mem_" + realvalue(find_by_name_hint(it2->first))) ) << ") ";
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
			fprintf(ftmp, "(get-value (%s))\n", it->c_str());
		}

		fprintf(ftmp, "(get-value (%s))\n", idx_content.c_str() );

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
			printf("number of iterations exceeded\n");
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
			string value = canonical_representation(result_get(line));
			printf("value_canonical_rep %s\n", value.c_str());

			sub_sol.insert(pair<string, int>(varname, stoi(value)));

		}
		
		i++;
		line = result[i];
		int idx_res = stoi(canonical_representation(result_get(line)));

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

