/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:38:08 PM
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


#include "solver.h"

#define SIZE_STR 32768
#define UNDERSCORE "_"
#define PAUSE_ON_INSERT false
#define EXIT_ON_INSERT false


extern Options* options;
extern Operators* operators;
extern Database* database;
extern Concurrency* concurrency;


Solver::Solver(){

	options->read_options();
	debug = options->cmd_option_bool("verbose");

}
Solver::~Solver(){}


void Solver::free_var(string var){

	if(!check_mangled_name(var)) assert(0 && "Wrong name for content");

	stringstream mem_name; mem_name << "mem_" << variables[var].content;
	forced_free_vars.insert( mem_name.str() );

}

string Solver::content( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if( variables[name].content == "" || is_forced_free(name) ){
		string position;
	        if(name.substr(0,7) == "global_")
			position = operators->get_actual_function() + UNDERSCORE + variables[name].name_hint;
		else
			position = variables[name].name_hint;
		insert_variable(name, position );

		if(is_number(name)) return name;
		else return position;
		//return name;

	} else {
		return variables[name].content;
	}
}


//void Solver::dump_variable(string position, string type, FILE* file){


		//bool is_pivot = false;
		//for( map<string,vector<string> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){
			//if(it->first == position)
				//is_pivot = true;
		//}

		////debug && printf("\e[31m dump_variable %s is_pivot %d\e[0m\n", position.c_str(), is_pivot);

		//if(is_pivot){
			//fprintf(file,"(declare-fun %s () %s)\n", locknames(position).c_str(), type.c_str());

			//vector<string> subst_to = pivot_variables[position];
			//for ( unsigned int i = 0; i < subst_to.size(); i++) {
				//string name = subst_to[i];
				//fprintf(file,"(declare-fun %s () %s)\n", locknames(name).c_str(), type.c_str());
			//}
		//} else {
			//fprintf(file,"(declare-fun %s () %s)\n", locknames(position).c_str(), type.c_str());
		//}

//}

void Solver::dump_pivots(FILE* file){

	//printf("dump pivots\n");

	for( map<string,vector<string> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){
		vector<string> vectorpivots = it->second;

		for( vector<string>::iterator it2 = vectorpivots.begin(); it2 != vectorpivots.end(); it2++ ){

			string hintpivot = *it2;
			string hint = hintpivot.substr(0, hintpivot.find("_pivot_"));
			string name = find_by_name_hint(hint);
			
			//printf("gettype %s %s\n", name.c_str(), get_type(name).c_str() );
			string type = get_type(name);
			//printf("gettype\n");
			fprintf(file, "(declare-fun %s () %s)\n", locknames(*it2).c_str(), type.c_str() );
		}
		

	}
	
}


void Solver::dump_variables(FILE* file){

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = get_type(it->name);

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", locknames(position).c_str(), type.c_str());

		
	}
	

}

void Solver::dump_conditions(FILE* file){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n", locknames(it->cond).c_str() );
	}
	
}

string Solver::find_mem_of_id(string id){


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(it->second.name_hint == id){
			return it->first;
		}
	}

	return "";
	
	

}

void Solver::dump_conditions( stringstream& sstr ){


	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		sstr << it->cond;
	}



}

void Solver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void Solver::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");

}

int Solver::minval(string type){

	if(type == "Int32") return -(1 << 30);
	if(type == "Int16") return -(1 << 15);
	if(type == "Int8")  return -(1 << 8);
	if(type == "Int") return   -(1 << 30);
	if(type == "Pointer") return 0;

	printf("MinVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;
}

int Solver::maxval(string type){

	if(type == "Int32") return (1 << 30);
	if(type == "Int16") return (1 << 15);
	if(type == "Int8") return (1 << 8);
	if(type == "Int") return (1 << 30);
	if(type == "Pointer") return (1 << 30);

	printf("MaxVal unknown type %s\n", type.c_str()); fflush(stdout);
	assert(0 && "Unknown type");
	return 0;

}

void Solver::dump_type_limits(FILE* file){


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = get_sized_type(it->name);

		string position = it->position;

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (< %s %d)))\n", position.c_str(), minval(type), position.c_str(), maxval(type) );
		
	}
}

void Solver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}

void Solver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n", locknames(it->position).c_str(), it->position.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if( it->second.content == "" ) continue;
		if( it->first.find("_pivot_") != string::npos ) continue;

		fprintf(file,"(get-value (%s)); %s\n", locknames(it->second.content).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	//for( set<string>::iterator it = forced_free_vars.begin(); it != forced_free_vars.end(); it++ ){
		//fprintf(file,"(get-value (%s));\n", get_first_content(*it).c_str() );
	//}
	
	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", it->second.c_str(), it->first.c_str());
	}
	
	
	
}

int Solver::get_num_fvars(){


	return free_variables.size();

}

string Solver::result_get(string get_str){


	get_str.erase(get_str.find_last_not_of(" \n\r\t")+1);

	vector<string> tokens = tokenize( get_str, "() ");

	if(tokens.size() < 2){
		printf("%s\n", get_str.c_str() );
		assert(0 && "result_get error");	
	}

	string ret;

	if( tokens[tokens.size() - 2] == "-" )
		ret = "-" + tokens[tokens.size() - 1];
	else 
		ret = tokens[tokens.size() - 1];

	assert( is_number(ret) && "Result is not a number");

	return ret;
}

void Solver::set_real_value(string varname, string value){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	//printf("set_real_value %s %s\n", varname.c_str(), value.c_str());
	variables[varname].real_value = value;
}

void Solver::set_real_value_mangled(string varname, string value ){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables[varname].real_value = value;
}

#define INITIAL_LINE_LENGTH	256
char* fgetln(register FILE* fp, size_t *lenp) {

	char c;
	size_t n, siz;
	size_t len, new_len;
	char *buf;
	char *p;

	len = INITIAL_LINE_LENGTH;
	n = siz = 0;

	if ((buf = (char*)malloc(INITIAL_LINE_LENGTH + 1)) == NULL)
		return (NULL);

	p = buf;
	for (;;) {
		if ((c = getc(fp)) == EOF) {
			if (siz != 0)
				break;
			free(buf);
			return (NULL);
		}

		++siz;

		if (c == '\n') {
			*p++ = c;
			break;
		}
		if (n++ >= len) {
			new_len = len << 1;
			if ((buf = (char*)realloc(buf, new_len + 1)) == NULL)
	                        return (NULL);
			len = new_len;
			p = buf;
	                p += len >> 1;
		}
		*p++ = c;
	}
	*p = 0;
	if (lenp != NULL)
		*lenp = siz;
	return (buf);
}

bool Solver::get_is_sat(string is_sat){

	if( is_sat == "sat" ) return true;
	else return false;
}

bool sat;

void Solver::solve_problem(){


	vector<string> ret_vector;

	sat = 0;

	stringstream filename;
	filename << "z3_" << rand() << ".smt2";

	debug && printf("\e[31m filename solve problem \e[0m %s\n", filename.str().c_str() );

	if(options->cmd_option_bool("see_each_problem"))
		getchar();

	FILE* file = fopen(filename.str().c_str(), "w");


	options->read_options();

	dump_header(file);
	dump_variables(file);
	dump_pivots(file);
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);

	fclose(file);

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];

	command << "z3 " << filename.str();

	fp = popen(command.str().c_str(), "r");

	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret)-1] = 0;
		ret_vector.push_back(ret);
	}

	//for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		//string line = *it;
		//if(line.find("error") != string::npos )
			//assert(0 && "Error in z3 execution");
	//}


	pclose(fp);

	string         sat_str       = ret_vector[0];

	if(sat_str.find("error") != string::npos )
		assert(0 && "Error in z3 execution");

	sat = get_is_sat(sat_str);

	if(!sat) return;


	bool sat = 0;


	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string varname = it->name;
		string value = result_get(*it_ret);


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);
		//variables[varname].real_value = value;

	}


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if( it->second.content == "" ) continue;
		if( it->first.find("_pivot_") != string::npos ) continue;
		//printf("first name %s\n", it->first.c_str() );

		string line = *it_ret;
		if(line.find("error") != string::npos )
			assert(0 && "Error in z3 execution");

		string name = it->first;
		string value = result_get(*it_ret);


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}


	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, result_get(*it_ret));

		it_ret++;
	}

}

bool Solver::solvable_problem(){


	return sat;
	
}

void Solver::set_sat(bool _sat){

	sat = _sat;
}

void Solver::insert_variable(string name, string position){



	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");


	if( name.find("constant") != string::npos )
		return;

	if( is_number(name) )
		return;

	//if(variables[name].contents.size() == 0)
		//return;
		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s\n", name.c_str(), variables[name].name_hint.c_str(), position.c_str() );

	if( PAUSE_ON_INSERT )
		getchar();

	if( EXIT_ON_INSERT )
		exit(0);

	NameAndPosition nandp = {name, position};
	free_variables.insert(nandp);

}

void Solver::push_condition(string cond, string fn, vector<string> joints ){


	set<string> joints_set = set<string>(joints.begin(), joints.end());

	Condition condition = { cond, fn, joints_set };
	conditions.push_back( condition );
}

string Solver::negation(string condition){


	stringstream negation_ss;
	negation_ss << "(not " << string(condition) << ")";

	return negation_ss.str();
}

string Solver::name_without_suffix( string name ){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}

string Solver::get_sized_type(string name){


	if( !check_mangled_name(name) ) assert(0 && "Wrong name for sized type");

	if (variables[name].type == "IntegerTyID32")
		return "Int32";

	if (variables[name].type == "IntegerTyID8")
		return "Int8";

	if (variables[name].type == "IntegerTyID16")
		return "Int16";

	if (variables[name].type == "FloatTyID")
		return "Float32";

	if (variables[name].type == "DoubleTyID")
		return "Float64";

	if (variables[name].type == "Int")
		return "Int";

	if (variables[name].type == "PointerTyID")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), variables[name].type.c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

void Solver::clean_conditions_stack(string name){

	
	for( vector<Condition>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->joints.find(name) != it->joints.end() ){
			conditions.erase(it);
			it--;
		}
	}
	

}

string Solver::realvalue_mangled(string varname){


	//printf("\e[33m realvalue_mangled \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue_mangled");


	if( varname.find("constant") != string::npos ){
		return varname.substr(9);
	} else if( variables[varname].real_value == "" ){
		return "0";
	} else {
		return variables[varname].real_value;
	}
}

string Solver::realvalue(string varname){


	//printf("\e[33m realvalue \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue");

	if(is_number(varname)){
		return varname;
	} else if( varname.find("constant") != string::npos ){
		//printf("constant\n");
		return varname.substr(9);
	} else if( variables[varname].real_value == "" ){
		//printf("empty\n");
		return "0";
	}else{
		//printf("else\n");
		if( variables.find(varname) == variables.end() ){
			assert(0 && "Variable not found");
		}
		return variables[varname].real_value;
	}

}

void Solver::set_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for set_is_propagated_constant");

	variables[varname].is_propagated_constant = true;

}

bool Solver::is_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for is_constant");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

void Solver::setcontent(string varname, string content){


	debug && printf("\e[31m setcontent %s %s\e[0m.\n", varname.c_str(), content.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for setcontent");
	variables[varname].content = content;
}

bool Solver::is_forced_free(string position){

	if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

	if( forced_free_vars.find(position) != forced_free_vars.end() ){
		if( already_forced_free.find(position) != already_forced_free.end() ){
			return false;
		} else{
			already_forced_free.insert(position);
			return true;
		}
	} else {
		return false;
	}

}

void Solver::load_forced_free_vars(){

	FILE *file = fopen ( "free_vars", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		forced_free_vars.insert(string(line));
	}
	fclose ( file );
	
}

//void Solver::substitute_pivots(string& src){

	//for( map<string,vector<string> >::iterator it = pivot_variables.begin(); it != pivot_variables.end(); it++ ){
		////printf("subst_pivot %s\n", it->first.c_str() );
		////if( get_name_hint(src) == it->first ){
		//if( src == it->first ){
			//vector<string> pivots = it->second;
			//string subst_to = pivots[pivots.size()-1];
			//printf("\n\e[33m Substitute_pivot_point\e[0m %s %s\n", it->first.c_str(), subst_to.c_str());
			//src = subst_to;
			////set_name_hint(src, subst_to);
		//}
	//}

//}

//bool Solver::is_pivot(string src){
	////string content_var = variables[src].content;
	////if(content_var.find("_pivot_") == string::npos)
	//if(src.find("_pivot_") == string::npos)
		//return false;
	//else
		//return true;
	////printf("is_pivot %s\n", content(src).c_str());
//}

void Solver::set_first_content(string src, string content){

	printf("\e[36m set_first_content %s %s\e[0m\n", src.c_str(), content.c_str());

	first_content[src] = content;

}

void Solver::set_first_content_value(string var, string value){
	printf("\e[36m set_first_content_value %s %s\e[0m\n", var.c_str(), value.c_str() );
	first_content_value[var] = value;
}

string Solver::get_first_content_value(string var){
	return first_content_value[var];
}

string Solver::get_first_content(string src){

	return first_content[src];

}

void Solver::assign_instruction(string src, string dst, string fn_name){

	//substitute_pivots(src);
	

	if(!check_mangled_name(src)) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for assign");


	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n",dst.c_str(),src.c_str() );

	//if( !is_pivot(src) ){
		//printf("not pivot\n");
		
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

	//} else {
		//printf("pivot\n");
		//variables[dst].content = variables[src].content;
	//}



	//if( variables[dst].type == "" ) assert(0 && "No type in dst");
	settype(dst, get_type(src));

	//printf("set_real_value inside assign %s %s %s\n", dst.c_str(), src.c_str(), realvalue(src).c_str() );
	set_real_value( dst, realvalue(src) );


	if( (get_is_propagated_constant(src) || is_constant(src)) && !is_forced_free(src) )
		set_is_propagated_constant(dst);


	//printf("srctree %s\n", get_offset_tree(src).c_str());

	set_offset_tree(dst, get_offset_tree(src));


	//debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[dst].content.c_str(), variables[dst].type.c_str() );
	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d %d\n",
                 variables[dst].content.c_str(), variables[dst].type.c_str(), realvalue(dst).c_str(), 
		 get_is_propagated_constant(src), get_is_propagated_constant(dst));



}

bool Solver::implemented_operation(string operation){

	if(operation == "+" ) return true;
	if(operation == "<=") return true;
	if(operation == ">=") return true;
	if(operation == "<" ) return true;
	if(operation == ">" ) return true;
	if(operation == "=" ) return true;
	if(operation == "#" ) return true;
	if(operation == "+" ) return true;
	if(operation == "-" ) return true;
	if(operation == "*" ) return true;
	if(operation == "/" ) return true;
	if(operation == "%" ) return true;
	if(operation == "R" ) return true;
	if(operation == "L" ) return true;
	if(operation == "Y" ) return true;
	if(operation == "X" ) return true;

	printf("operation %s\n", operation.c_str());
	return false;
}

void Solver::binary_instruction(string dst, string op1, string op2, string operation){

	//substitute_pivots(op1);
	//substitute_pivots(op2);

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(op1)) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(op2)) assert(0 && "Wrong op2 for binary_instruction");
	if(!implemented_operation(operation)) assert(0 && "Not implemented operation");

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s (%s %s)\e[0m\n",
			dst.c_str(),op1.c_str(), operation.c_str(),op2.c_str(),
		        get_type(op1).c_str(), get_type(op2).c_str() );


	stringstream content_ss;


	if( operation == "#" ){
		content_ss << "(not (= " << content(op1 ) << " " <<  content(op2 ) << "))";
	} else if (operation == "%") {
		content_ss << "(mod " << content(op1 ) << " " <<  content(op2 ) << ")";
	} else if (operation == "R" ) {

		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_number(op2)) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2 );
		int factor = 1 << exponent;

		content_ss << "(/ " << content(op1) << " " << factor << ")";

	} else if (operation == "L" ) {

		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_number(op2)) assert(0 && "Rotate non-constant");
		int exponent = stoi( op2 );
		int factor = 1 << exponent;

		content_ss << "(* " << content(op1) << " " << factor << ")";

	} else if (operation == "Y" ) {
		assert(0 && "Non-Supported Operation");
	} else if (operation == "X" ) {
		assert(0 && "Non-Supported Operation");
	} else {
		content_ss << "(" << operation << " " << content(op1 ) << " " <<  content(op2 ) << ")";
	}

	//debug && printf("\e[31m type \e[0m %s \e[31m op2 \e[0m %s \e[31m operation \e[0m %s\n", variables[op1].type.c_str(), op2.c_str(), operation.c_str() );
	

	variables[dst].content = content_ss.str();

	if( variables[op1].type != "" )
		settype(dst, get_type(op1));
	else
		settype(dst, get_type(op2));


	if( get_is_propagated_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( get_is_propagated_constant(op1) && is_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( is_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}



	if(operation == "<="){
		set_real_value(dst, ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == ">="){
		set_real_value(dst, ( stoi(realvalue(op1) ) >= stoi( realvalue(op2) ) )?"true":"false" );
	}


	if(operation == "<"){
		set_real_value(dst, ( stoi(realvalue(op1) ) < stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == ">"){
		set_real_value(dst, ( stoi(realvalue(op1) ) > stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == "="){
		set_real_value(dst, ( stoi(realvalue(op1) ) == stoi( realvalue(op2) ) )?"true":"false" );
	}

	if(operation == "#"){
		set_real_value(dst, ( stoi(realvalue(op1) ) != stoi( realvalue(op2) ) )?"true":"false" );
	}


	if(operation == "+"){

		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");

		set_real_value(dst, result.str());
	}

	if(operation == "-"){


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) - stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}

	if(operation == "*"){

		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) * stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) * stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	}


	if(operation == "/"){


		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) / stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) / stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");

		set_real_value(dst, result.str());
	}


	if(operation == "%"){
		stringstream result; result << stoi(realvalue(op1)) % stoi(realvalue(op2));
		set_real_value(dst, result.str());
	}

	if(operation == "R"){
		//if(op2.substr(0,9) != "constant" UNDERSCORE) assert(0 && "Rotate non-constant");
		if(!is_number(op2)) assert(0 && "Rotate non-constant");
		int places = stoi( op2 );

		int result_i = stoi(realvalue(op1)) >> places;

		stringstream result; result << result_i;
		set_real_value(dst, result.str());

		//printf("rotate %s %s\n", realvalue(op1).c_str(), result.str().c_str());

	}

	if( operation == "Y" ){
		int op1_i = stoi(realvalue(op1));
		int op2_i = stoi(realvalue(op2));
		int res = op1_i & op2_i;
		stringstream result; result << res;
		set_real_value(dst, result.str());
	}


	if( variables[op1].type != "" ) variables[dst].type = variables[op1].type;
	if( variables[op2].type != "" ) variables[dst].type = variables[op2].type;


	if( variables[op1].type == "bool" && op2 == "0" && operation == "#" ){
		debug && printf("\e[32m Propagation of bool constraint \e[0m\n");

		content_ss.str("");
		content_ss << content(op1);
		variables[dst].content = content_ss.str();

		set_real_value(dst, realvalue(op1) );
	}




	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d\n",
                 variables[dst ].content.c_str(), variables[dst].type.c_str(), realvalue(dst).c_str(),
		get_is_propagated_constant(dst) );


}

int Solver::show_problem(){


	options->read_options();
	
	dump_header();
	dump_variables();
	dump_pivots();
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits();
	dump_conditions();
	dump_check_sat();
	//dump_get();
	dump_tail();






	stringstream filename; filename << "z3-" << rand() << ".smt2";

	debug && printf("\e[31m filename \e[0m %s\n", filename.str().c_str() );

	FILE* file = fopen(filename.str().c_str(), "w");

	dump_header(file);
	dump_variables(file);
	dump_pivots(file);
	//concurrency->dump_remaining_variables(free_variables, file);
	dump_type_limits(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_tail(file);

	fclose(file);



	fflush(stdout);

	getchar();
}

string Solver::get_offset_tree( string varname ){

	//assert(check_mangled_name(varname) && "Incorrect name for get_offset_tree");
	//printf("get_offset_tree %s %s\n", varname.c_str(), variables[varname].tree.c_str() );
	return variables[varname].tree;
}

bool Solver::check_mangled_name(string name){

	//printf("check_mangled_name %s\n", name.c_str());

	if(name.find("pivot") != string::npos) return true;

	int number_of_underscore = count(name, UNDERSCORE);
	if(
			number_of_underscore != 1 && // main_registerunderscoreval mem_9
			number_of_underscore != 0    // 0
	)
		return false;

	if( number_of_underscore == 1 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[1].substr(0,8) != "register" &&
		   tokens[0].substr(0,3) != "mem"      &&
		   tokens[0].substr(0,6) != "global"
		  ) return false;
	}

	if( number_of_underscore  == 0 ){
		if( !is_number(name) )
			return false;
	}

	if( number_of_underscore  == 6 ){
		if(name.find("pivot") == string::npos)
			return false;
	}

	return true;

}

bool Solver::get_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for get_is_propagated_constant");
	return variables[varname].is_propagated_constant;
}

string Solver::gettype(string name){

	if(name.find("_pivot_") != string::npos)
		name = name.substr(0, name.find("_pivot_"));

	return variables[name].type;
}

void Solver::set_name_hint(string name, string hint){

	variables[name].name_hint = hint;
}

string Solver::get_name_hint(string name){

	//debug && printf("\e[33m get_name_hint %s %s\e[0m\n", name.c_str(), variables[name].name_hint.c_str() );

	return variables[name].name_hint;
}

string Solver::find_by_name_hint(string hint){

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		//printf("find_by_name_hint %s %s %s\n", it->first.c_str(), it->second.name_hint.c_str(), it->second.content.c_str() );

		if(it->second.name_hint == hint /*|| it->first == hint*/)
			return it->first;
	}
	
	assert(0 && "name not found");

	return "";
	
}

void Solver::set_offset_tree( string varname, string tree ){

	//assert(check_mangled_name(varname) && "Incorrect name for set_offset_tree");
	//printf("set_offset_tree %s %s\n", varname.c_str(), tree.c_str() );
	variables[varname].tree = tree;
}

void Solver::settype(string name, string type){


	if( !check_mangled_name(name) ) assert(0 && "Wrong name for settype");
	variables[name].type = type;

}

string Solver::get_type(string name){

	if(name.find("pivot") != string::npos)
		name = name.substr(0,name.find("_pivot_"));

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for type");

	if(name.substr(0,9) == "constant" UNDERSCORE) return "IntegerTyID32";
	if( is_number(name) ){

		if( name.find(".") != string::npos )
			return "FloatTyID";
		else
			return "IntegerTyID32";
	}

	if (gettype(name) == "IntegerTyID32")
		return "Int";

	if (gettype(name) == "DoubleTyID")
		return "Real";

	if (gettype(name) == "IntegerTyID64")
		return "Int";

	if (gettype(name) == "IntegerTyID8")
		return "Int";

	if (gettype(name) == "IntegerTyID16")
		return "Int";

	if (gettype(name) == "PointerTyID")
		return "Int";

	if (gettype(name) == "Int")
		return "Int";

	if (gettype(name) == "FloatTyID")
		return "Real";

	if (gettype(name) == "Real")
		return "Real";

	if (gettype(name) == "bool")
		return "bool";

	if (gettype(name) == "Pointer")
		return "Pointer";


	printf("name %s type %s\n", name.c_str(), gettype(name).c_str() );

	assert(0 && "Unknown Type");

	return "Int";

}

vector<bool> Solver::get_path_stack(){

	return path_stack;
}

void Solver::push_path_stack(bool step){

	path_stack.push_back(step);
}

void Solver::print_path_stack(){



	printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		printf("%s", (*it)?"T":"F" );
	}
	printf("\n");

	printf("\e[33m Depth \e[0m %lu\n", path_stack.size());
	

}

map<string, Variable> Solver::get_map_variables(){

	return variables;
}

vector<Condition> Solver::get_stack_conditions(){

	return conditions;
}

set<NameAndPosition> Solver::get_free_variables(){
	return free_variables;
}

string Solver::get_position(string name){


	return variables[name].name_hint;

}

void Solver::pivot_variable(string variable, string name){


	debug && printf("\e[33m pivot_variable %s %s\e[0m\n", variable.c_str(), name.c_str());

	string origname = variable;
	string orig_content = content(origname);

	string hint = get_name_hint(variable);

	string pivot_name = hint + "_pivot_" + name;
	setcontent(pivot_name, origname);
	setcontent(origname,orig_content);
	
	vector<string> empty;
	stringstream condition; condition << "(= " << pivot_name << " " << orig_content << ")";
	push_condition(condition.str(), "", empty);

	pivot_variables[variable].push_back(pivot_name);


	debug && printf("\e[31m pivot_variable %s %s\e[0m %s %s %s\n", variable.c_str(), name.c_str(), origname.c_str(), orig_content.c_str(), variables[origname].content.c_str() );
}

