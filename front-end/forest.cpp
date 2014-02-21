/*
 * =====================================================================================
 * /
 * |     Filename:  forest.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/21/2013 12:35:23 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *      ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include "forest.h"


#define SIZE_STR 512

#define debug false

using namespace std;


typedef struct FreeVariableInfo{
	string name;
	string type;
	string position;

} FreeVariableInfo;


std::map<std::string, std::string> options; // Opciones del fichero XML / linea de comandos

std::map<string, vector<string> > needed_map;
std::map<string, set<string> > disables_map;
std::set<string> passes_done;

string project_path;
string current_path;


void do_pass(string passname){

	if(passname == "make_bc")
		make_bc();
	else if(passname == "run")
		run();
	else if(passname == "vim")
		vim();
	else if(passname == "test")
		test();
	else if(passname == "clean")
		clean();
	else if(passname == "final")
		final();
	else if(passname == "measure_coverage")
		measure_coverage();
	else if(passname == "check_coverage")
		check_coverage();
	else if(passname == "klee")
		do_klee();
	else if(passname == "get_result")
		get_result();
	else {
		printf("Pass %s\n", passname.c_str());
		assert(0 && "Unknown pass");
	}
}

bool done(string passname){
	return passes_done.find(passname) != passes_done.end();
}

void start_pass(string pass){

	debug && printf(" ----- Starting pass %s\n", pass.c_str());


	vector<string> needed = needed_map[pass];
	for( vector<string>::iterator it = needed.begin(); it != needed.end(); it++ ){
		debug && printf("pass %s needs %s\n", pass.c_str(), it->c_str() );
		if(!done(*it)){
			debug && printf("Do it (%s)\n", it->c_str());
			//set_option(*it, "true");
			//options_to_file();
			do_pass(*it);
		} else {
			debug && printf("Already done (%s)\n", it->c_str());
		}
	}
}

void end_pass(string passname){
	debug && printf(" ----- Ending pass %s\n", passname.c_str());
	passes_done.insert(passname);
}

vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

void set_option( string key, string value ){
	options[key] = value;
}

void load_cmd_options(int argc, const char** argv ){


	if( argc >= 2 && argv[1][0] != '-' ){
		argc = argc - 1;
		argv = argv + 1;
	}
	
	vector<string> tokens; // palabras de la linea de comandos
	
	for( int n = 1/**/; n < argc; n++ ){
		char* token_str; // elemento de la linea de comandos
		if( argv[n][0] == '-' && argv[n][1] != '-' )
			token_str = (char*)argv[n];
		else if( argv[n][0] == '-' && argv[n][1] == '-' )
			token_str = (char*)argv[n]+1;
		else
			token_str = (char*)argv[n];
		
		string token( token_str ); // cada palabra de la linea de comandos
		tokens.push_back( token );	
	}
	
	
	for( unsigned int n = 0/**/; n < tokens.size(); ){
		if( tokens[n][0] == '-' && ( (int)n+2 == argc || tokens[n+1][0] == '-' ) ){
			options[ tokens[n].substr(1) ] = "true";
			n++;
			continue;
		}
		
		if( tokens[n][0] == '-' && tokens[n+1][0] != '-' ){
			options[ tokens[n].substr(1) ] = tokens[n+1];
			n++;n++;
			continue;
		}
	}
	
	
	
	
}

int cmd_option_int(string option){
	return atoi( options[option].c_str() );
}

string cmd_option_str(string option){
	if(options[option] == "" ) return "";
	vector<string> tokens = tokenize(options[option].c_str(),"@" );
	string ret = tokens[tokens.size()-1];
	return ret;
}

bool cmd_option_bool(string option){
	return options[option] == "true" || options[option] == "True" ;
}

float cmd_option_float(string option){
	return atof( options[option].c_str() );
}

vector<string> cmd_option_string_vector(string option){
	return tokenize( options[option], "@" );
}

vector<int> cmd_option_int_vector(string option){
	vector<string> vector_str = tokenize( options[option], "@");
	vector<int> vector_int;

	for ( unsigned int i = 0; i < vector_str.size(); i++) {
		vector_int.push_back( atoi( vector_str[i].c_str() ) );
	}
	return vector_int;
}

vector<float> cmd_option_float_vector(string option){
	vector<string> vector_str = tokenize( options[option], "@");
	vector<float> vector_float;

	for ( unsigned int i = 0; i < vector_str.size(); i++) {
		vector_float.push_back( atof( vector_str[i].c_str() ) );
	}
	return vector_float;
}

void load_file_options(string file){


	TiXmlDocument doc(file.c_str()); // documento xml
	doc.LoadFile();
	
	std::string m_name; // nombre
	
	TiXmlHandle hDoc(&doc); // handler del xml
	TiXmlElement* pElem; // cada elemento
	TiXmlHandle hRoot(0); // raiz del xml
	
	pElem=hDoc.FirstChildElement("options").Element();
	m_name=pElem->Value();
	
	hRoot=TiXmlHandle(pElem);

	pElem=hRoot.FirstChild().Element();
	for( ; pElem; pElem=pElem->NextSiblingElement()){


		bool found = false;
		for( map<string, string>::iterator it = options.begin(); it != options.end(); it++){


			if( it->first == pElem->Attribute("key") ){
				found = 1;
				break;
			} else {
				found = 0;
			}
		}


		if(found){
			options[pElem->Attribute("key")] += ( string( "@" ) + pElem->Attribute("value") );
		} else {
			options[pElem->Attribute("key")] = pElem->Attribute("value");
		}


	}
	
}

void load_default_options(){
	options["verbose"] = "false";
	options["base_path"] = "/media/disk/release";
	options["llvm_path"] = "/llvm-2.9";
	options["output_file"] = "final";
	options["tmp_dir"] = "/tmp/forest";
	options["subst_names"] = "true";
	options["propagate_constants"] = "true";
	//options["compare_klee"] = "true";
	//options["get_result"] = "true";
}

void load_file_options(){
	load_file_options(string("config.xml"));
}

void cmd_option_set(string key, string value ){

	options[key] = value;


}

void systm( string cmd ){

	//if( cmd_option_bool("verbose") ){
		//printf("\e[31m %s \e[0m\n", cmd.c_str() );
		//fflush(stdout);
	//}

	stringstream command;

	command << "(";

	command << "cd " << cmd_option_str("tmp_dir") << "; ";
	
	if( cmd_option_bool("verbose") )
		command << cmd;
	else
		command << "(" << cmd << ") >/dev/null 2>/dev/null";

	command << ")";

	if( cmd_option_bool("verbose") ){
		printf("\e[31m %s \e[0m\n", command.str().c_str() );
		fflush(stdout);
	}

	int ret = system(command.str().c_str() );

	//if(ret != 0) exit(0);

}

string tmp_file(string file){
	return cmd_option_str("tmp_dir") + "/" + file;
}

string prj_file(string file){
	return project_path + "/" + file;
}

void clean(){

	start_pass("clean");

	stringstream cmd;

	// Crea y limpia la carpeta temporal
	cmd.str("");
	cmd << "rm -rf " << cmd_option_str("tmp_dir") << "/*;";
	cmd << "mkdir -p " << cmd_option_str("tmp_dir") << ";";
	systm(cmd.str().c_str());

	end_pass("clean");

}

bool is_bc(string file){
	int len = file.length();
	string suffix = file.substr(len-3);
	return suffix == ".bc";
}


void make_initial_bc(){

	stringstream cmd;

	string llvm_path = cmd_option_str("llvm_path");

	if( is_bc(cmd_option_string_vector("file")[0]) ){
		// Copia el bc a la carpeta temporal
		cmd.str("");
		cmd << "cp ";
		cmd << prj_file(cmd_option_str("file"));
		cmd << " " << tmp_file("file.bc");
		systm(cmd.str().c_str());
	} else {
		// Junta todos los .c en uno
		cmd.str("");
		cmd << "cat ";
		vector<string> files = cmd_option_string_vector("file");
		for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
			cmd << prj_file(*it) << " ";
		}
		cmd << "> " << tmp_file("file.cpp");
		systm(cmd.str().c_str());



		string base_path = cmd_option_str("base_path");


		string cflags;
		if(cmd_option_bool("with_libs"))
			cflags = "-I" + base_path + "/stdlibs/include/";


		// Compilación del código a .bc
		cmd.str("");
		cmd << "llvm-g++ -O0 --emit-llvm -D NO_INIT " << cflags << " -c file.cpp -o file.bc";
		systm(cmd.str().c_str());



		if(cmd_option_bool("with_libs")){

			// Cambio de nombre de las funciones estándar
			cmd.str("");
			cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_function_names < file.bc > file-2.bc";
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "llvm-link " << tmp_file("file-2.bc") << " " << base_path << "/stdlibs/lib/library.bc -o " << tmp_file("file-3.bc") << ";";
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "mv " << tmp_file("file-3.bc") << " " << tmp_file("file.bc");
			systm(cmd.str().c_str());
		}


	}
}


void make_initial_bc_klee(){

	stringstream cmd;

	// Junta todos los .c en uno
	cmd.str("");
	cmd << "cat ";
	vector<string> files = cmd_option_string_vector("file");
	for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
		cmd << prj_file(*it) << " ";
	}
	cmd << "> " << tmp_file("file.cpp");
	systm(cmd.str().c_str());



	string base_path = cmd_option_str("base_path");


	// Compilación del código a .bc
	cmd.str("");
	cmd << "llvm-g++ -O0 --emit-llvm -D KLEE -c file.cpp -o file.bc";
	systm(cmd.str().c_str());

}




void make_bc(){

	start_pass("make_bc");

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	if(cmd_option_str("seed_function") != ""){
		cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -isolate_function < file.bc > file-2.bc";
		systm(cmd.str().c_str());
		cmd.str("");
		cmd << "mv file-2.bc file.bc";
		systm(cmd.str().c_str());
	}

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	end_pass("make_bc");

}

void compare_bc(){

	start_pass("compare_bc");


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());


	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-3.bc > salida2.txt";
	systm(cmd.str().c_str());


	// Comparación
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());


	end_pass("compare_bc");

}

void compare_measure_bc(){


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());


	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-3.bc > salida2.txt";
	systm(cmd.str().c_str());


	// Comparación
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());



}

void view_bc(){

	start_pass("view_bc");

	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());

	// Visualizar
	cmd.str("");
	cmd << "gedit salida1.txt &";
	systm(cmd.str().c_str());

	end_pass("view_bc");

}

void final(){

	start_pass("final");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	stringstream cmd;

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc file-3.bc -o file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c file-3.s -o file-3.o";
	systm(cmd.str().c_str());

	// linka
	cmd.str("");
	cmd << "g++ file-3.o " << base_path << "/lib/forest.a" << " -lpthread -ldl -lrt -o " << output_file;
	systm(cmd.str().c_str());

	end_pass("final");

}

void dump_forced_free_vars(){
	vector<string> forced_free_vars = cmd_option_string_vector("forced_free_var");

	stringstream filepath;

	filepath << tmp_file("free_vars");

	FILE* file = fopen(filepath.str().c_str(), "w");
	for( vector<string>::iterator it = forced_free_vars.begin(); it != forced_free_vars.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
}


void vim(){

	start_pass("vim");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	dump_forced_free_vars();

	stringstream cmd;

	set_option("verbose", "true");
	options_to_file();

	// Ejecuta el fichero resultante
	cmd.str("");
	cmd << "./" << output_file << " > output;";
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "gvim +AnsiEsc " << "output;";
	systm(cmd.str().c_str());

	end_pass("vim");

}

typedef struct PathAndConds {
	string path;
	string conds;
	int width;

} PathAndConds;

inline bool operator<(const PathAndConds& lhs, const PathAndConds& rhs) {
	if(lhs.width != rhs.width) return lhs.width > rhs.width;
	return lhs.path < rhs.path;
}


set<string> heuristics;

void load_heuristics(){

	printf("load_heuristics\n");

	ifstream input("/tmp/heuristics");
	string line;
	
	while( getline( input, line ) ) {
		heuristics.insert(line);
	}
	
}

set<string> vtos(vector<string> vect){
	set<string> ret;
	for( vector<string>::iterator it = vect.begin(); it != vect.end(); it++ ){
		ret.insert(*it);
	}

	return ret;
	
}

set<string> setintersection(set<string> set_a, set<string> set_b){


	printf("setintersection\n");

	for( set<string>::iterator it = set_a.begin(); it != set_a.end(); it++ ){
		printf("%s,", it->c_str() );
	} printf("\n");
	
	for( set<string>::iterator it = set_b.begin(); it != set_b.end(); it++ ){
		printf("%s,", it->c_str() );
	} printf("\n");


	set<string> ret;
	for( set<string>::iterator it = set_a.begin(); it != set_a.end(); it++ ){
		if(set_b.find(*it) != set_b.end()) ret.insert(*it);
	}

	return ret;
	
}

int width(string conds){
	vector<string> tokens = tokenize(conds, ",");
	set<string> tokens_set = vtos(tokens);

	return setintersection( tokens_set,heuristics).size();
}

void add_paths(set<PathAndConds>& frontier){

	stringstream action;

	action << "echo 'select path from frontend;' | sqlite3 database.db > paths";
	systm(action.str());

	action.str("");
	action << "echo 'select conditions from frontend;' | sqlite3 database.db > conditions";
	systm(action.str());

	string line;

	vector<string> paths;
	vector<string> conds;

	{
		ifstream input("/tmp/forest/paths");
		while( getline( input, line ) ) {
			paths.push_back(line);
		}
	}
	
	{
		ifstream input("/tmp/forest/conditions");
		while( getline( input, line ) ) {
			conds.push_back(line);
		}
	}


	assert(paths.size() == conds.size());

	for ( unsigned int i = 0; i < paths.size(); i++) {
		PathAndConds path_and_cond = {paths[i], conds[i], width(conds[i])};
		frontier.insert(path_and_cond);
	}




}

void get_static_heuristic(){

	make_initial_bc();

	stringstream cmd;
	string llvm_path   = cmd_option_str("llvm_path");

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());


	// Paso de optimización de la heuristica
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestHeuristic.so -pathfinder < file.bc > file-2.bc";
	systm(cmd.str().c_str());



}

void print_frontier(set<PathAndConds> frontier){

	printf("frontier: ");
	for( set<PathAndConds>::iterator it = frontier.begin(); it != frontier.end(); it++ ){
		printf("%s:(%s%d), ", it->path.c_str(), it->conds.c_str(), it->width);
	}
	printf("\n");
}

string get_last_bb(){
	stringstream command;
	command << "echo 'select last_bb from frontend;' | sqlite3 database.db > /tmp/last_bb";
	systm(command.str().c_str());
	

	ifstream input("/tmp/last_bb");
	string line;
	
	input >> line;

	return line;


	
}

void drive_frontend(){

	printf("drive_frontend\n");

	set_option("follow_path", "true");
	set_option("single_step", "true");

	set<PathAndConds> frontier;

	load_heuristics();

	int n = 0;
	do {
		PathAndConds first;
		if(frontier.size()){
			first = *(frontier.begin());
			frontier.erase(frontier.begin());
		}

		set_option("path", first.path);

		options_to_file();

		// Ejecuta el fichero resultante
		stringstream cmd;
		cmd << "./" << cmd_option_str("output_file");
		systm(cmd.str().c_str());

		add_paths(frontier);
		print_frontier(frontier);

		if(n++ == cmd_option_int("max_depth"))
			exit(0);

		printf("last_bb %s\n", get_last_bb().c_str() );
		if(get_last_bb() == cmd_option_str("target_node")){
			printf("Node hitted\n");
			exit(0);
		}


	} while(frontier.size());

}

void run(){

	start_pass("run");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	dump_forced_free_vars();

	stringstream cmd;

	// Ejecuta el fichero resultante
	cmd.str("");
	cmd << "./" << output_file;


	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	if(cmd_option_bool("driven_by_frontend")){
		drive_frontend();
	} else {
		systm(cmd.str().c_str());
	}

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e9;
	spent_time *= 1000;

	stringstream action;
	action << "insert into measurements values(\"time_ms\"," << (int)spent_time << ");";
	db_command( action.str() );
	


	minimal_test_vectors_to_db();

	end_pass("run");

}

void db_command(string command){

	cmd_option_bool("verbose") && printf("\e[32m db_command %s \e[0m\n", command.c_str());

	stringstream cmd;
	cmd << "echo '" << command << "' | sqlite3 " << tmp_file("database.db");
	systm(cmd.str().c_str());

}

void show_results(){


	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd << "echo \'.mode columns\\n.width 25 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;\'";
	cmd << " | sqlite3 " << tmp_file("database.db");



	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		printf("%s", it->c_str());
	}
	



}


void show_coverage(){


	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd.str("");
	db_command( ".mode columns\\n.width 20 15\\n.headers on\\nselect * from measurements;" );



	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		printf("%s", it->c_str());
	}
	



}




void test(){

	start_pass("test");

	string explanation = cmd_option_str("explanation") + " ";

	while( explanation.length() < 55 )
		explanation = explanation + ".";

	printf("* Testing %s", explanation.c_str() );

	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd.str("");
	cmd << "echo '.mode columns\\n.width 25 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << "> " << tmp_file("results");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "diff results " << prj_file("gold_result") << " > /dev/null";
	int result = system(cmd.str().c_str());

	if( result )
		printf("\e[31m Failed :( \e[0m\n");
	else
		printf("\e[32m Passed :) \e[0m\n");

	end_pass("test");
}

void set_current_path(){
	char current_path_c[SIZE_STR];
	strcpy(current_path_c, getenv("PWD"));
	current_path = string(current_path_c);

	cmd_option_bool("verbose") && printf("current_path %s\n", current_path.c_str());
}


void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

void set_project_path( string file ){

	vector<string> tokens = tokenize(file, "/");

	string path_aux = "/";

	for ( unsigned int i = 0; i < tokens.size() - 1; i++) {
		path_aux += tokens[i] + "/";
	}

	project_path = path_aux;
	if(project_path == ""){
		project_path = current_path;
	} else {
		project_path = project_path.substr(0, project_path.length()-1);
		myReplace(project_path, "/./", current_path + "/");
	}

	cmd_option_bool("verbose") && printf("project_path %s\n", project_path.c_str());
	

}

void view_dfg(){


	stringstream cmd;


	make_initial_bc();





	// paso de optimización dot
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "cd " << cmd_option_str("tmp_dir") << "; ";
	command << "opt -dot-cfg < file.bc 2>&1 | grep Writing";
	
	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	
	vector<string> gen_dfgs;

	if(cmd_option_str("dfg_function") == ""){
		for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
			vector<string> tokens = tokenize(*it, "'");
			gen_dfgs.push_back(tokens[1]);
		}
	} else {
		gen_dfgs.push_back("cfg." + cmd_option_str("dfg_function") + ".dot");
	}
	
	

	for( vector<string>::iterator it = gen_dfgs.begin(); it != gen_dfgs.end(); it++ ){

		// pasa el dot a png
		cmd.str("");
		cmd << "dot -T png " << *it << " > " << *it << ".png";
		systm(cmd.str().c_str());

		// Visualiza el png
		cmd.str("");
		cmd << "eog " << *it << ".png &";
		systm(cmd.str().c_str());
		
	}

}


void view_dfg_2(){


	stringstream cmd;


	make_initial_bc();

	string llvm_path = cmd_option_str("llvm_path");

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());



	// paso de optimización dot
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "cd " << cmd_option_str("tmp_dir") << "; ";
	command << "opt -dot-cfg < file-3.bc 2>&1 | grep Writing";
	
	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	
	vector<string> gen_dfgs;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "'");
		gen_dfgs.push_back(tokens[1]);
	}
	
	

	for( vector<string>::iterator it = gen_dfgs.begin(); it != gen_dfgs.end(); it++ ){

		// pasa el dot a png
		cmd.str("");
		cmd << "dot -T png " << *it << " > " << *it << ".png";
		systm(cmd.str().c_str());

		// Visualiza el png
		cmd.str("");
		cmd << "eog " << *it << ".png &";
		systm(cmd.str().c_str());
		
	}

}


bool covers_bool( vector<string> v1, vector<string> v2 ){

	debug && printf("\e[31m coversbool \e[0m\n");
	for( vector<string>::iterator it = v1.begin(); it != v1.end(); it++ ){
		debug && printf("%s ", it->c_str() );
	}
	debug && printf(" -- ");
	for( vector<string>::iterator it = v2.begin(); it != v2.end(); it++ ){
		debug && printf("%s ", it->c_str() );
	}
	
	
	for ( unsigned int i = 0; i < v1.size(); i++) {
		//printf("%s %s ", v1[i].c_str(), v2[i].c_str() );
		if( v1[i] != v2[i] && v1[i] != "X" && v2[i] != "X" ){
			debug && printf("not cover\n"); //getchar();
			return false;
		}
	}

	debug && printf("cover\n"); //getchar();

	return true;
}

vector<string> covers( vector<string> v1, vector<string> v2 ){

	vector<string> ret;


	//for( vector<string>::iterator it = v1.begin(); it != v1.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	//printf(" -- ");
	//for( vector<string>::iterator it = v2.begin(); it != v2.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	
	
	for ( unsigned int i = 0; i < v1.size(); i++) {
		/*if( v1[i] == "X" && v2[i] == "X" ){*/
			//ret.push_back( "0" );
		/*} else*/ if( v1[i] == "X" ){
			ret.push_back( v2[i] );
		} else if( v2[i] == "X" ){
			ret.push_back( v1[i] );
		} else {
			if( v1[i] != v2[i] ){printf("ERROR\n"); exit(0);}
			ret.push_back( v1[i] );
		}

	}

	//printf(" -- ");
	//for( vector<string>::iterator it = ret.begin(); it != ret.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	//printf("\n"); //getchar();

	return ret;

}

bool dontcares( vector<string> v ){

	for( vector<string>::iterator it = v.begin(); it != v.end(); it++ ){
		if( *it == "X" )
			return true;
	}

	return false;

}

void printvector( vector<string> v ){


	for( vector<string>::iterator it = v.begin(); it != v.end(); it++ ){
		printf("%s ", it->c_str() );
	} printf("\n");
	

}

set<vector<string> > minimal_vectors(){

	// Obtenemos los resultados de la base de datos
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;

	if(project_path != "")
		command << "cd " << project_path << ";";


	command << "echo 'select name,value,problem_id from results where is_free;' | sqlite3 " << tmp_file("database.db");
	fp = popen(command.str().c_str(), "r");
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	pclose(fp);


	// Obtenemos los nombres
	set<string> names;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		string name = tokens[0];
		names.insert(name);
	}

	
	// por cada problema, una relación entre nombre de variable, y valor
	map< int, map<string, string> > values;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		string name = tokens[0];
		string value = tokens[1];
		int problem_id; sscanf(tokens[2].c_str(), "%d", &problem_id);
		values[problem_id][name] = value;
	}


	// Cambio los "" por X
	debug && printf("\e[31m Map \e[0m\n");
	for( map<int,map<string, string> >::iterator it = values.begin(); it != values.end(); it++ ){
		for( set<string>::iterator name = names.begin(); name != names.end(); name++ ){
			if( it->second[*name] == "" ) it->second[*name] = "X";
			debug && printf(" %s ", it->second[*name].c_str() );
		}
		debug && printf("\n");
		
	}

	// Lo paso a un set de vectores
	set<vector<string> > values_set;
	for( map<int,map<string, string> >::iterator it = values.begin(); it != values.end(); it++ ){
		vector<string> insert_vec;
		for( set<string>::iterator name = names.begin(); name != names.end(); name++ ){
			insert_vec.push_back( it->second[*name].c_str() );
		}
		values_set.insert(insert_vec);
	}

	debug && printf("\e[31m Set \e[0m\n");
	for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
		vector<string> v = *it;
		for( vector<string>::iterator it2 = v.begin(); it2 != v.end(); it2++ ){
			debug && printf("%s  ", it2->c_str());
		}
		debug && printf("\n");
	}
	



	// Elimino los tests que son cubiertos por otro
	
	int prev_size, size;

	while(true){

		int prev_size = values_set.size();

		set<vector<string> > to_insert;
		set<vector<string> > to_remove;

		debug && printf("\e[31m Prunning iteration \e[0m\n");








		debug && printf("\e[32m names \e[0m\n");
		for( set<string>::iterator it = names.begin(); it != names.end(); it++ ){
			debug && printf("%s ", it->c_str());
		}
		debug && printf("\n\e[32m values \e[0m\n");
		for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
			vector<string> row = *it;
			for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
				debug && printf("%s  ", it2->c_str() );
			}
			debug && printf("\n");
		}














		for( set<vector<string> >::iterator v1 = values_set.begin(); v1 != values_set.end(); v1++ ){
			for( set<vector<string> >::iterator v2 = values_set.begin(); v2 != values_set.end(); v2++ ){


				if( *v1 == *v2 ) continue;

				if( !dontcares(*v1) ){
					if(debug){ printf("\e[34m Insert nodc \e[0m"); printvector( *v1 ); }
					to_insert.insert(*v1);
				}

				if( dontcares(*v1) || dontcares(*v2) ){

					if(debug){printf("\e[31m v1 \e[0m "); printvector(*v1);}
					if(debug){printf("\e[31m v2 \e[0m "); printvector(*v2);}

					if( covers_bool(*v1, *v2) ){

						to_remove.insert(*v1);
						to_remove.insert(*v2);
						to_insert.insert( covers(*v1, *v2) );

						if(debug){ printf("\e[34m remove \e[0m "); printvector(*v1); }
						if(debug){ printf("\e[34m remove \e[0m "); printvector(*v2); }
						if(debug){ printf("\e[34m Insert  \e[0m"); printvector( covers(*v1, *v2) ); }

					}

				}

			}

		}

		debug && printf("values_set.size() %lu\n", values_set.size());
		debug && printf("toremove.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_remove.begin(); it != to_remove.end(); it++ ){
			if(debug){ printf("remove "); printvector(*it); }
			values_set.erase( values_set.find(*it) );
		}

		debug && printf("toinsert.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_insert.begin(); it != to_insert.end(); it++ ){
			if(debug){ printf("insert "); printvector(*it); }
			values_set.insert( *it );
		}

		debug && printf("\n\e[32m values \e[0m\n");
		for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
			vector<string> row = *it;
			for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
				debug && printf("%s  ", it2->c_str() );
			}
			debug && printf("\n");
		}

		int size = values_set.size();

		if( size == prev_size ) break;
	}

	set<vector<string> > values_set2;
	for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
		vector<string> vect = *it;
		vector<string> vect2;
		for( vector<string>::iterator it2 = vect.begin(); it2 != vect.end(); it2++ ){
			if(*it2 == "X")
				vect2.push_back("0");
			else
				vect2.push_back(*it2);
		}
		values_set2.insert(vect2);
		
	}

	return values_set2;
	
}

vector<FreeVariableInfo> get_free_variables(){

	stringstream cmd;

	cmd.str("");

	if(project_path != "")
		cmd << "cd " << project_path << ";";

	cmd << "echo 'select name,type,position from variables group by name;' | sqlite3 " << tmp_file("database.db");

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<FreeVariableInfo> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret) - 1 ] = 0;

		vector<string> tokens = tokenize(string(ret), "|");

		string name = tokens[0];
		string type = tokens[1];
		string position = tokens[2];

		FreeVariableInfo fvi = {name, type, position};

		ret_vector.push_back(fvi);

	}
	
	pclose(fp);

	return ret_vector;

}

void gen_file_free_variables(){


	vector<FreeVariableInfo> ret_vector = get_free_variables();

	vector<string> outfile;
	for( vector<FreeVariableInfo>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		outfile.push_back( it->name + " " + it->type + " " + it->position );
	}

	string filename;

	filename = tmp_file("free_variables");

	FILE* file = fopen(filename.c_str(), "w");

	for( vector<string>::iterator it = outfile.begin(); it != outfile.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);

}

vector< map<string, string> > vector_of_test_vectors(){

	vector<map<string, string> > ret;

	vector<FreeVariableInfo> free_variables = get_free_variables();
	set<vector<string> > test_vectors = minimal_vectors();

	for( set<vector<string> >::iterator it = test_vectors.begin(); it != test_vectors.end(); it++ ){
		map<string, string> mapa;
		for ( unsigned int i = 0; i < free_variables.size(); i++) {
			string var_name = free_variables[i].name;
			string value = (*it)[i];

			mapa[var_name] = value;
		}
		ret.push_back(mapa);
	}

	return ret;

}

void gen_file_vectors(){

	set<vector<string> > vectors = minimal_vectors();

	vector<string> output_file;
	for( set<vector<string> >::iterator it = vectors.begin(); it != vectors.end(); it++ ){
		vector<string> vect = *it;

		string line;
		for( vector<string>::iterator it2 = vect.begin(); it2 != vect.end(); it2++ ){
			line += *it2 + " ";
		}
		
		output_file.push_back(line);
	}


	string filename;

	filename = tmp_file("vectors");

	FILE* file = fopen( filename.c_str(), "w");
	for( vector<string>::iterator it = output_file.begin(); it != output_file.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
	

}

void gen_final_for_measurement(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc file-3.bc -o file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c file-3.s -o file-3.o";
	systm(cmd.str().c_str());

	// linka
	cmd.str("");
	cmd << "g++ file-3.o " << base_path << "/lib/forest.a -lpthread -ldl -o " << output_file;
	systm(cmd.str().c_str());

}

void measure_coverage(){

	start_pass("measure_coverage");

	gen_file_free_variables();
	gen_file_vectors();
	gen_final_for_measurement();

	set_option("measurement", "true");
	options_to_file();

	// Ejecuta
	
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());

	end_pass("measure_coverage");
	

}

void show_test_vectors(){

	//db_command(".mode columns\\n.width 6 30 5\\n.headers on\\nselect * from minimal_vectors;");
	
	stringstream command;

	command << "(";

	command << "cd " << cmd_option_str("tmp_dir") << "; ";

	command << "echo '" << ".mode columns\\n.width 6 20 30 5\\n.headers on\\nselect * from minimal_vectors;" << "' | sqlite3 " << tmp_file("database.db");

	command << ")";
	
	int ret = system(command.str().c_str() );

}

void create_table_minimal_test_vectors(){


	db_command("drop table minimal_vectors;");
	db_command( "create table minimal_vectors (vector_id Integer, variable varchar(50), hint varchar(50), value varchar(50));" );

}

string get_position(string name){


	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << "; echo 'select position from variables where name = \"" << name << "\" limit 1;' | sqlite3 database.db";

	char ret[SIZE_STR];
	FILE *fp = popen(cmd.str().c_str(), "r");
	fscanf(fp, "%s", ret);
	pclose(fp);

	return string(ret);
	
}

void minimal_test_vectors_to_db(){

	create_table_minimal_test_vectors();

	vector< map<string, string> > vectors = vector_of_test_vectors();

	int vect = 0;
	for( vector<map<string, string> >::iterator it = vectors.begin(); it != vectors.end(); it++,vect++ ){
		for( map<string,string>::iterator it2 = (*it).begin(); it2 != (*it).end(); it2++ ){
			//printf("%s -> %s\n", it2->first.c_str(), it2->second.c_str() );

			int vectid = vect;
			string name = it2->first;
			string value = it2->second;
			string hint = get_position(name);

			stringstream cmd;
			cmd << "insert into minimal_vectors values (" << vect << ",\"" << name << "\",\"" << hint << "\",\"" << value << "\");";
			db_command(cmd.str());

			//systm( cmd.str() );

			//printf("%s\n", cmd.str().c_str() );



		}
		
		
	}
}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

void check_coverage(){

	start_pass("check_coverage");

	vector<string> coverages;

	coverages.push_back("fn");
	coverages.push_back("bb");

	for( vector<string>::iterator it = coverages.begin(); it != coverages.end(); it++ ){

		string cov = *it;

		int expected_coverage = cmd_option_int("expected_" + cov + "_coverage");

		stringstream cmd;

		// Muestro los resultados de la base de datos
		cmd.str("");
		if(project_path != "")
			cmd << "cd " << project_path << ";";
		cmd << "echo 'select value from measurements where key = \"visited_" + cov + "s\";' | sqlite3 " << tmp_file("database.db");



		FILE *fp;
		stringstream command;
		char ret[SIZE_STR];
		vector<string> ret_vector;

		fp = popen(cmd.str().c_str(), "r");

		while (fgets(ret,SIZE_STR, fp) != NULL)
			ret_vector.push_back(ret);

		pclose(fp);

		assert( ret_vector.size() && "No coverage measurements");

		vector<string> tokens = tokenize( *(ret_vector.begin()), " ");

		string coverage_s = tokens[2];

		int archived_coverage = stoi(coverage_s);



		string explanation = cmd_option_str("explanation") + " ";

		while( explanation.length() < 51 )
			explanation = explanation + ".";

		printf("* Coverage of %s", explanation.c_str() );


		if( archived_coverage <  expected_coverage ) printf("\e[31m Less coverage than expected :( (%d < %d)\e[0m\n", archived_coverage, expected_coverage);
		if( archived_coverage >  expected_coverage ) printf("\e[33m More coverage than expected :S (%d > %d)\e[0m\n", archived_coverage, expected_coverage);
		if( archived_coverage == expected_coverage ) printf("\e[32m Same coverage as expected :) (%d)\e[0m\n", archived_coverage);

	}

	end_pass("check_coverage");

}

void gen_file_free_variables_from_xml(){

	vector<string> free_variables = cmd_option_string_vector("random_variable");


	string filename;

	filename = tmp_file("free_variables");

	FILE* file = fopen(filename.c_str(), "w");


	for( vector<string>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file, "%s\n", it->c_str() );
	}

	fclose(file);

}

int custom_random(string name, map<string, string> distributions){


	vector<string> tokens = tokenize( distributions[name], " ");
	string distribution = tokens[0];

	//printf("distribution %s %s\n", name.c_str(), distribution.c_str());

	if( distribution == "uniform" ){

		int min_r = stoi(tokens[1]);
		int max_r = stoi(tokens[2]);
		int ret = (rand() % (max_r-min_r)) + min_r;

		return ret;

	}

	assert(0 && "Unknown distribution");


}

void gen_file_vectors_random(){

	string filename;

	filename = tmp_file("vectors");

	FILE* file = fopen(filename.c_str(), "w");

	vector<string> types;
	vector<string> names;
	vector<string> free_variables = cmd_option_string_vector("random_variable");
	for( vector<string>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");
		types.push_back(tokens[1]);
		names.push_back(tokens[0]);
	}

	map<string, string> distributions_map;
	vector<string> distributions = cmd_option_string_vector("distribution");
	for( vector<string>::iterator it = distributions.begin(); it != distributions.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");

		string distribution;
		for ( unsigned int i = 1; i < tokens.size(); i++) {
			distribution += " " + tokens[i];
		}

		distributions_map[tokens[0]] = distribution;
	}







	for ( unsigned int i = 0; i < cmd_option_int("num_random_vectors"); i++) {
		for ( unsigned int j = 0; j < types.size(); j++) {
			string type = types[j];
			string name = names[j];
			if( type == "Int32" ){
				fprintf(file, "%d ", (int)custom_random(name, distributions_map) );
			} else if( type == "Int16" ){
				fprintf(file, "%d ", (short)custom_random(name, distributions_map) );
			} else if( type == "Int8"){
				fprintf(file, "%d ", (char)custom_random(name, distributions_map) );
			} else {
				assert(0 && "Unknown type");
			}
		}

		fprintf(file, "\n");
		
	}
	



	fclose(file);


}

void random_testing(){

	gen_file_free_variables_from_xml();
	gen_file_vectors_random();
	gen_final_for_measurement();

	set_option("measurement", "true");
	options_to_file();


	// Ejecuta
	
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" + output_file;
	systm(cmd.str().c_str());

}


void count_branches(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_countbr < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc file-3.bc -o file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c file-3.s -o file-3.o";
	systm(cmd.str().c_str());

	// linka
	cmd.str("");
	cmd << "g++ file-3.o " << base_path << "/lib/measurement.a -lpthread -ldl -o " << output_file;
	systm(cmd.str().c_str());

	// ejecuta
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());

}

void do_klee(){

	start_pass("klee");

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc_klee();

	// Ejecutar klee
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;

	command << "(cd " << cmd_option_str("tmp_dir") << "; klee --emit-all-errors file.bc 2>&1)";

	cmd_option_bool("verbose") && printf("\e[31m %s \e[0m\n", command.str().c_str());
	

	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	fp = popen(command.str().c_str(), "r");
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	pclose(fp);

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e9;
	int time_ms_int = (int)(spent_time*1000.0);
	//int time_ms_int = (int)(spent_time);

	
	// Número de caminos ejecutados
	int completed_paths;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->find("completed paths") != string::npos ){
			completed_paths = stoi(it->substr( it->find("=")+1 ));
		}
	}

	// Guardar los valores en la base de datos
	db_command( "create table klee( time_ms Integer, paths Integer );" );
	cmd.str("");
	cmd << "insert into klee values('" << time_ms_int << "','" << completed_paths << "');";
	db_command(cmd.str());



	cmd.str("");
	cmd << "ktest-tool --write-ints klee-last/test*.ktest";
	systm(cmd.str());




	end_pass("klee");

}


void gen_final_for_concurrency(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");
	stringstream cmd;

		make_initial_bc();

	// Compilación del código a .bc
	cmd.str("");
	cmd << "llvm-g++ -O0 --emit-llvm -c file.cpp -o file.bc";
	systm(cmd.str().c_str());

	// Primer paso de optimización (concurrencia)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_all < file.bc > file-2.bc";
	systm(cmd.str().c_str());


	// Segundo paso de optimización (exploración)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc file-3.bc -o file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c file-3.s -o file-3.o";
	systm(cmd.str().c_str());

	// linka
	cmd.str("");
	cmd << "g++ file-3.o " << base_path << "/lib/forest.a -lpthread -ldl -lrt -o " << output_file;
	systm(cmd.str().c_str());


}

void view_bc_concurrency(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");
	stringstream cmd;

	make_initial_bc();

	// Primer paso de optimización (concurrencia)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_all < file.bc > file-2.bc";
	systm(cmd.str().c_str());


	// Segundo paso de optimización (exploración)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());


	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-3.bc > salida1.txt";
	systm(cmd.str().c_str());

	// Visualizar
	cmd.str("");
	cmd << "gedit salida1.txt &";
	systm(cmd.str().c_str());


}



void compare_concurrency(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file.bc > salida1.txt";
	systm(cmd.str().c_str());

	// Paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_all < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida2.txt";
	systm(cmd.str().c_str());

	// Comparación
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());


}

void extract_concurrency(){

	gen_final_for_concurrency();

	run();

}

void options_to_file(){

	FILE* file = fopen("/tmp/options", "w");

	for( map<string,string>::iterator it = options.begin(); it != options.end(); it++ ){
		fprintf(file, "%s %s\n", it->first.c_str(), it->second.c_str());
	}
	fclose(file);
}

void show_concurrency_table(){

	db_command(".mode columns\\n.width 15 5 10 35\\n.headers on\\nselect * from concurrency;");
	db_command(".mode columns\\n.width 15 10 35\\n.headers on\\nselect * from stores;");
	db_command(".mode columns\\n.width 15 20\\n.headers on\\nselect * from sync;");
	db_command(".mode columns\\n.width 15 20\\n.headers on\\nselect * from global_types;");
	
}

void clean_concurrency(){

	db_command("drop table concurrency;");
	db_command("drop table loads;");
	db_command("drop table stores;");
	db_command("drop table sync;");
	db_command("drop table global_types;");

	stringstream action;
	action << "create table concurrency(";
	action << "lockunlock varchar(50),";
	action << "mutex_name varchar(50),";
	action << "sync_name  varchar(50),";
	action << "conds      varchar(50)";
	action << ");";
	action << "create table loads(";
	action << "pos varchar(50)";
	action << ");";
	action << "create table stores(";
	action << "pos varchar(50),";
	action << "value varchar(50),";
	action << "sync_point varchar(50)";
	action << ");";
	action << "create table sync(";
	action << "pos varchar(50),";
	action << "stack varchar(50)";
	action << ");";
	action << "create table global_types(";
	action << "pos varchar(50),";
	action << "type varchar(50),";
	action << "position varchar(50)";
	action << ");";


	db_command( action.str() );
}

void secuencialize(){

	string fn_seq = cmd_option_str("seq_name");
	cmd_option_bool("verbose") && printf("secuencializing function %s\n", fn_seq.c_str());


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Paso de optimización secuencialización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -secuencialize < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// paso de optimización (fillnames)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// paso de optimización (exploracion)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-3.bc > file-4.bc";
	systm(cmd.str().c_str());

	
	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc file-4.bc -o file-4.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c file-4.s -o file-4.o";
	systm(cmd.str().c_str());

	string output_file = cmd_option_str("output_file");

	// linka
	cmd.str("");
	cmd << "g++ file-4.o " << base_path << "/lib/forest.a " << "-lpthread -ldl -lrt -o " << output_file;
	systm(cmd.str().c_str());


	dump_forced_free_vars();

	// Ejecuta el fichero resultante
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());










}

void compare_secuencialize(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file.bc > salida1.txt";
	systm(cmd.str().c_str());

	// Paso de optimización (secuencialización)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -secuencialize < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida2.txt";
	systm(cmd.str().c_str());

	// Comparación
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());
}

void check_sync_tables(){

	string explanation = cmd_option_str("explanation") + " ";

	while( explanation.length() < 50 )
		explanation = explanation + ".";

	printf("* Concurrency %s", explanation.c_str() );

	stringstream cmd;

	cmd.str("");
	cmd << "echo === Concurrency: === >> " << tmp_file("results_sync") << ";";
	cmd << "echo '.mode columns\\n.width 15 5 20 35\\n.headers on\\nselect * from concurrency;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << ">> " << tmp_file("results_sync");
	cmd << "; echo >> " << tmp_file("results_sync");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "echo === Stores: === >> " << tmp_file("results_sync") << ";";
	cmd << "echo '.mode columns\\n.width 15 10 35\\n.headers on\\nselect * from stores;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << ">> " << tmp_file("results_sync");
	cmd << "; echo >> " << tmp_file("results_sync");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "echo === Sync: === >> " << tmp_file("results_sync") << ";";
	cmd << "echo '.mode columns\\n.width 15 60\\n.headers on\\nselect * from sync;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << ">> " << tmp_file("results_sync");
	cmd << "; echo >> " << tmp_file("results_sync");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "echo === Global_Types: === >> " << tmp_file("results_sync") << ";";
	cmd << "echo '.mode columns\\n.width 25 10 20\\n.headers on\\nselect * from global_types;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << ">> " << tmp_file("results_sync");
	cmd << "; echo >> " << tmp_file("results_sync");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "diff results_sync " << prj_file("gold_sync") << " > /dev/null";
	int result = system(cmd.str().c_str());

	//printf("check_sync_tables %s\n", cmd.str().c_str());

	if( result )
		printf("\e[31m Concurrency Failed :( \e[0m\n");
	else
		printf("\e[32m Concurrency Passed :) \e[0m\n");



}

void get_concurrent_functions(){


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// Paso de optimización (get_concurrent_functions)
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -get_concurrent < file.bc > file-2.bc";
	systm(cmd.str().c_str());

}

void get_concurrent_info(){

	get_concurrent_functions();

	string filename = tmp_file("concurrent_functions");
	//printf("filename %s\n", filename.c_str());
	FILE *file = fopen ( filename.c_str(), "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	vector<string> concurrent_functions;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		concurrent_functions.push_back(string(line));
	}
	fclose ( file );
	
	for( vector<string>::iterator it = concurrent_functions.begin(); it != concurrent_functions.end(); it++ ){
		set_option("seedfn", it->c_str());
		set_option("concurrency", "true");
		options_to_file();
		gen_final_for_concurrency();


		dump_forced_free_vars();

		stringstream cmd;
		// Ejecuta el fichero resultante
		cmd.str("");
		cmd << "./" << cmd_option_str("output_file");
		systm(cmd.str().c_str());

		//check_sync_tables();
		//exit(0);

	}
	


}

void check_concurrency(){
	//start_pass("check_concurrency");
	clean();
	clean_concurrency();
	get_concurrent_info();
	check_sync_tables();
	//end_pass("check_concurrency");

}

void check_c2(){

	string explanation = cmd_option_str("explanation") + " ";

	while( explanation.length() < 50 )
		explanation = explanation + ".";

	printf("* Concurrency2 %s", explanation.c_str() );

	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd.str("");
	cmd << "echo '.mode columns\\n.width 20 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << "> " << tmp_file("results");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "diff results " << prj_file("gold_result") << " > /dev/null";
	int result = system(cmd.str().c_str());

	if( result )
		printf("\e[31m Failed :( \e[0m\n");
	else
		printf("\e[32m Passed :) \e[0m\n");

}


void secuencialize_fn1(){
	set_option("secuencialize", "true");
	set_option("seq_name", "_Z3fn1Pv");
	set_option("see_each_problem", "true");
	options_to_file();
	//load_file_options();
	secuencialize();
}

void check_concurrency_2(){
	system("eog syncgraph.svg 2>/dev/null &");
	clean();
	clean_concurrency();
	get_concurrent_info();
	secuencialize_fn1();
	check_c2();
}

void needs(string second, string first){
	needed_map[second].push_back(first);
}

void disables(string second, string first){
	disables_map[second].insert(first);
}

void compare_klee(){

	start_pass("compare_klee");


	int paths_klee;
	int paths_forest;
	int time_klee;
	int time_forest;

	stringstream command;
	
	{
		command.str("");
		command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select paths from klee;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &paths_klee);
		pclose(fp);
	}
	
	{
		command.str("");
		command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select count(distinct vector_id) from minimal_vectors;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &paths_forest);
		pclose(fp);
	}


	{
		command.str("");
		command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select time_ms from klee order by rowid desc limit 1;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &time_klee);
		pclose(fp);
	}

	{
		command.str("");
		command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select value from measurements where key=\"time_ms\";' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &time_forest);
		pclose(fp);
	}



	string explanation = cmd_option_str("explanation") + " ";
	while( explanation.length() < 50 )
		explanation = explanation + ".";
	printf("* Comparing %s", explanation.c_str() );

	char color_p[] = "\e[0m";
	char color_t[] = "\e[0m";
	
	if(paths_forest < paths_klee)
		strcpy(color_p, "\e[31m"); // rojo
	else if(paths_forest > paths_klee)
		strcpy(color_p, "\e[32m"); // verde
	else
		strcpy(color_p, "\e[33m"); // amarillo

	if(time_forest > time_klee)
		strcpy(color_t, "\e[31m"); // rojo
	else if(time_forest < time_klee)
		strcpy(color_t, "\e[32m"); // verde
	else
		strcpy(color_t, "\e[33m"); // amarillo





	printf("%s Paths_klee %-3d Paths_forest %-3d\e[0m %s Time_klee %-3d Time_forest %-3d\e[0m\n", color_p, paths_klee, paths_forest, color_t, time_klee, time_forest);

	end_pass("compare_klee");

}

void expand_options(){

	for ( unsigned int i = 0; i < 10; i++) {
		for( map<string,set<string> >::iterator it = disables_map.begin(); it != disables_map.end(); it++ ){
			string a = it->first;
			set<string> b = it->second;
			for( set<string>::iterator it2 = b.begin(); it2 != b.end(); it2++ ){
				if(cmd_option_bool(a)) set_option(*it2, "false");
			}
		}
	}

}

void get_result(){
	start_pass("get_result");

	stringstream cmd;
	cmd << "cp " << tmp_file("results") << " " << prj_file("gold_result");
	systm(cmd.str());

	end_pass("get_result");
}

void compare_libs(){

	stringstream cflags;
	cflags << "-I " << cmd_option_str("base_path") << "/stdlibs/include/ -L" << cmd_option_str("base_path") << "/stdlibs/lib";
	stringstream cmd;

	cmd.str("");
	cmd << "llvm-g++ --emit-llvm " << prj_file(cmd_option_string_vector("file")[0]) << " -c -o " << tmp_file("file-1.bc") << ";";
	systm(cmd.str());

	cmd.str("");
	cmd << "llvm-g++ --emit-llvm " << cflags.str() << " " << prj_file(cmd_option_string_vector("file")[0]) << " -c -o " << tmp_file("file-2.bc") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "llvm-dis " << tmp_file("file-1.bc") << " -o " << tmp_file("file-1.ll") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "llvm-link " << tmp_file("file-2.bc") << " " << cmd_option_str("base_path") << "/stdlibs/lib/library.bc" << " -o " << tmp_file("file-3.bc") << ";";
	systm(cmd.str());

	cmd.str("");
	cmd << "llvm-dis " << tmp_file("file-3.bc") << " -o " << tmp_file("file-3.ll") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "meld file-1.ll file-3.ll";
	systm(cmd.str());


	

}

char get_argv_char(int testvector, int i){

	stringstream command;
	FILE *fp;
	char ret[SIZE_STR];

	command.str("");
	command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select value from minimal_vectors where vector_id=" << testvector << " and hint=\"main_register_argvs+" << i << "\";' | sqlite3 database.db";
	fp = popen(command.str().c_str(), "r");
	fscanf(fp, "%s", ret);
	pclose(fp);

	//printf("%s ", ret);

	if(string(ret) == "")
		return 0;
	else
		return stoi(ret);

}

void show_argvs(){

	int num_vectors;
	int max_size;
	stringstream command;
	FILE *fp;
	char ret[SIZE_STR];

	command.str("");
	command << "cd " << cmd_option_str("tmp_dir") << "; echo 'select count(distinct vector_id) from minimal_vectors;' | sqlite3 database.db";
	fp = popen(command.str().c_str(), "r");
	fscanf(fp, "%d", &num_vectors);
	pclose(fp);

	string argvs_str = cmd_option_str("sym_argvs");
	string max_size_each_s = tokenize(argvs_str, " ")[2];
	string max_size_s = tokenize(argvs_str, " ")[1];
	max_size = stoi(max_size_s) * stoi(max_size_each_s) + stoi(max_size_s);


	for ( unsigned int testvector = 0; testvector < num_vectors; testvector++) {

		printf("Testcase %3d : ", testvector);
		for ( unsigned int i = 0; i < max_size; i++) {
			
			char argv_char = get_argv_char(testvector, i);
			
			if((unsigned char)argv_char <  32){ printf("\e[1;37m\\%X\e[0m", (unsigned char)argv_char); continue; }
			if((unsigned char)argv_char > 126){ printf("\e[1;37m\\%X\e[0m", (unsigned char)argv_char); continue; }

			printf("%c", argv_char);

		}
		printf("\n");
	}

}

vector<string> get_model_paths(){

	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "echo 'select path from models;' | sqlite3 database.db";
	cmd << " > model_paths";
	system(cmd.str().c_str());

	vector<string> lines;
	string line;

	ifstream input((cmd_option_str("tmp_dir") + "/model_paths").c_str());
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}
	
	return lines;
	
}


vector<string> get_model_assigns(){

	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "echo 'select content from models;' | sqlite3 database.db";
	cmd << " > model_assigns";
	system(cmd.str().c_str());

	vector<string> lines;

	ifstream input((cmd_option_str("tmp_dir") + "/model_assigns").c_str());
	string line;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}
	
	

	return lines;
	
}


vector<string> get_model_names(){

	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "echo 'select variable from models;' | sqlite3 database.db";
	cmd << " > model_variables";
	system(cmd.str().c_str());

	ifstream input((cmd_option_str("tmp_dir") + "/model_variables").c_str());
	string line;
	vector<string> lines;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}

	return lines;
	
}

set<string> get_model_freevars(){

	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "echo 'select free from models;' | sqlite3 database.db";
	cmd << " > model_free";
	system(cmd.str().c_str());

	FILE *file = fopen ( (cmd_option_str("tmp_dir") + "/model_free").c_str() , "r" );
	static char line [ 50000 ]; /* or other suitable maximum line size */
	vector<string> lines;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		lines.push_back(string(line));
	}
	fclose ( file );

	set<string> free_vars;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		vector<string> tokens = tokenize(*it, ",");
		for( vector<string>::iterator it2 = tokens.begin(); it2 != tokens.end(); it2++ ){
			free_vars.insert(*it2);
		}
		
	}
	

	return free_vars;

}

set<string> get_model_outputs(){

	stringstream cmd;
	cmd << "cd " << cmd_option_str("tmp_dir") << ";";
	cmd << "echo 'select variable from models;' | sqlite3 database.db";
	cmd << " > model_outputs";
	system(cmd.str().c_str());

	FILE *file = fopen ( (cmd_option_str("tmp_dir") + "/model_outputs").c_str() , "r" );
	static char line [ 50000 ]; /* or other suitable maximum line size */
	vector<string> lines;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		lines.push_back(string(line));
	}
	fclose ( file );

	set<string> outputs;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		outputs.insert(*it);
		
	}
	

	return outputs;

}

void and_paths(vector<string>& paths){
	
	for ( unsigned int i = 0; i < paths.size(); i++) {
		vector<string> paths_v = tokenize(paths[i], ",");
		string path;

		path = "(and ";
		for ( unsigned int k = 0; k < paths_v.size(); k++) {
			path += ( paths_v[k] + " " );
		}
		path += ")";

		paths[i] = path;
	}
	
}

void get_model(){

	vector<string> paths   = get_model_paths();
	vector<string> assigns = get_model_assigns();
	vector<string> names   = get_model_names();
	set<string>    free_v  = get_model_freevars();
	set<string>    outputs = get_model_outputs();

	and_paths(paths);

	//printf("paths and models %lu %lu\n", paths.size(), assigns.size());

	assert(paths.size() == assigns.size());
	assert(paths.size() == names.size());

	stringstream model;
	model << "content:(assert (or ";

	for ( unsigned int i = 0; i < paths.size(); i++) {
		string path = paths[i];
		string assign = assigns[i];
		string name = names[i];

		model << "(and " << "(= " << name << " " << assign << ") " << path << ")";
	}
	model << "))";

	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		printf("input:%s\n", it->c_str());
	}

	for( set<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){
		printf("output:%s\n", it->c_str());
	}
	

	printf("%s\n", model.str().c_str());


	
}

typedef struct Node {
	string cond_pos;
	int node_pos;
	int node_neg;
	string assign;
} Node;

typedef vector<string> Path;

typedef struct PathAndAssign {
	Path path;
	string assign;
} PathAndAssign;


vector<string> remove(vector<string>input , string to_remove){
	vector<string> ret;
	for( vector<string>::iterator it = input.begin(); it != input.end(); it++ ){
		if(*it != to_remove)
			ret.push_back(*it);
	}
	return ret;
}

string negation(string cond){
	if(cond.substr(0,4) == "(not"){
		string right = cond.substr(5);
		string center = right.substr(0, right.length()-1);
		return center;
	} else {
		return "(not " + cond + ")";
	}
}

bool is_complete(string variable, vector<PathAndAssign> table){

	for( vector<PathAndAssign>::iterator it = table.begin(); it != table.end(); it++ ){
		PathAndAssign path_and_assign = *it;
		Path path = path_and_assign.path;
		bool found = false;
		for( Path::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			if(*it2 == variable || negation(*it2) == variable)
				found = true;
		}
		if(!found) return false;
		
	}
	
	return true;
}

bool contains_pos(Path path, string cond){
	for( Path::iterator it = path.begin(); it != path.end(); it++ ){
		if( cond == *it )
			return true;
	}

	return false;
	
}

bool contains_neg(Path path, string cond){
	for( Path::iterator it = path.begin(); it != path.end(); it++ ){
		if( "(not " + cond + ")" == *it )
			return true;
	}

	return false;
	
}

void part_paths(string cond, vector<PathAndAssign> input, vector<PathAndAssign>& output_pos, vector<PathAndAssign>& output_neg ){

	for( vector<PathAndAssign>::iterator it = input.begin(); it != input.end(); it++ ){
		Path path = it->path;
		if( contains_pos(path, cond) )
			output_pos.push_back(*it);
		else if( contains_neg(path, cond))
			output_neg.push_back(*it);
		else
			assert(0 && "Malformed BDD");
	}
	
	
}


PathAndAssign tail(PathAndAssign path_and_assign){

	PathAndAssign ret = path_and_assign;
	Path::iterator it_begin = path_and_assign.path.begin() + 1;
	Path::iterator it_end   = path_and_assign.path.end();
	Path retpath = Path(it_begin, it_end);
	ret.path = retpath;

	return ret;
}

string positive_cond(string condition){
	if(condition.substr(0,5) == "(neg ") return negation(condition);
	return condition;
}

void show_bdd(vector<Node> nodes, string title = ""){

		FILE* file = fopen("/tmp/digraph", "w");
		fprintf(file, "digraph G{\n");
		for ( unsigned int i = 0; i < nodes.size(); i++) {
			Node n = nodes[i];

			if(nodes[i].node_pos != -1 ) fprintf(file, "%d -> %d [color=\"green\"]\n", i, nodes[i].node_pos );
			if(nodes[i].node_neg != -1 ) fprintf(file, "%d -> %d [color=\"red\"]\n",   i, nodes[i].node_neg );
			//if(nodes[i].node_pos != -1 ) fprintf(file, "%d -> %d [color=\"red\"]\n", i, nodes[i].node_pos );
			//if(nodes[i].node_neg != -1 ) fprintf(file, "%d -> %d [color=\"green\"]\n",   i, nodes[i].node_neg );

		}

		fprintf(file, "legend_1 [shape=none, margin=0, label=<");
		fprintf(file, "<table border='0' cellborder='0'>");

		if(title != ""){
			fprintf(file, "<tr><td>");
			fprintf(file, "%s", title.c_str());
			fprintf(file, "</td></tr>\n");
		}


		for ( unsigned int i = 0; i < nodes.size(); i++) {


			if(nodes[i].node_pos == -1 && nodes[i].node_neg == -1 && nodes[i].assign == "")
				continue;

			stringstream row;
			string cond_pos = nodes[i].cond_pos; if(cond_pos == "") cond_pos = "-"; if(cond_pos.length() > 20) cond_pos = cond_pos.substr(0,20) + "...";
			string assign   = nodes[i].assign;   if(assign   == "") assign   = "-"; if(assign.length()   > 20) assign   =   assign.substr(0,20)  + "...";
			int node_pos = nodes[i].node_pos;
			int node_neg = nodes[i].node_neg;
			row << "<tr>"; 

			row << "<td align='left'>";
			row << i;
			row << "</td>";

			row << "<td align='left'>";
			row << "<font color='green'>" << cond_pos << "</font>";
			row << "</td>";

			row << "<td align='left'>";
			row << "<font color='blue'>" << assign << "</font>";
			row << "</td>";

			row << "</tr>"; 

			fprintf(file, "%s\n", row.str().c_str());

		}
		//fprintf(file, "<tr><td align='left'><font color='red'> hola </font></td></tr>");
		//fprintf(file, "<tr><td align='left'> adiosssss </td></tr>");
		fprintf(file, "</table>");
		fprintf(file, ">];");



		fprintf(file, "}\n");
		fclose(file);
		system("cat /tmp/digraph | dot -Tpng > /tmp/digraph.png 2>/dev/null");
		system("eog /tmp/digraph.png 2>/dev/null");
}

void print_path_assign(PathAndAssign pa){

	Path path = pa.path;
	string assign = pa.assign;
	for( vector<string>::iterator it = path.begin(); it != path.end(); it++ ){
		printf("%s ", it->c_str());
	}
	printf(": %s\n",assign.c_str());
	
}

void print_path(Path path){

	for( vector<string>::iterator it = path.begin(); it != path.end(); it++ ){
		printf("%s ", it->c_str());
	}
	printf("\n");
	
}

void insert_node(vector<Node>& nodes, Node node){
	//printf("insert_node %lu\n", nodes.size());
	nodes.push_back(node);
}

void new_node_pos(vector<Node>& nodes, int node_root){
	//printf("set node_pos %d %lu\n", node_root, nodes.size());
	nodes[node_root].node_pos = nodes.size();
}

void new_node_neg(vector<Node>& nodes, int node_root){
	//printf("set node_neg %d %lu\n", node_root, nodes.size());
	nodes[node_root].node_neg = nodes.size();
}

void add_path(vector<Node>& nodes, PathAndAssign path_and_assign, int node_root = 0){


	Path path = path_and_assign.path;
	string cond = path.size()? path[0]:"";
	string assign = path_and_assign.assign;


	if(!nodes.size()){
		Node node = {positive_cond(cond), -1, -1, ""};
		insert_node(nodes, node);
		add_path(nodes, path_and_assign, node_root);
	}

	bool follow_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos != -1);
	bool follow_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg != -1);
	bool create_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos == -1);
	bool create_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg == -1);
	bool is_terminal = (path.size() == 1);

	//printf("-----------\n");
	//printf("add_path\n");
	//print_path_assign(path_and_assign);
	//printf("node_root %d\n", node_root);
	//printf("cond %s\n", cond.c_str());
	//printf("follow_pos %d follow_neg %d create_pos %d create_neg %d is_terminal %d\n", follow_pos, follow_neg, create_pos, create_neg, is_terminal);

	//show_bdd(nodes);

	if(follow_pos && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		return;
	}

	if(follow_neg && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg);
		return;
	}

	if(create_pos){
		if(is_terminal){
			new_node_pos(nodes, node_root);
			Node node = { "", -1, -1, assign};
			insert_node(nodes, node);
		} else {
			new_node_pos(nodes, node_root);
			Node node = { positive_cond( path[1] ), -1, -1, ""};
			insert_node(nodes, node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		}
	}

	if(create_neg){
		if(is_terminal){
			new_node_neg(nodes, node_root);
			Node node = { "", -1, -1, assign};
			insert_node(nodes, node);
		} else {
			new_node_neg(nodes, node_root);
			Node node = {positive_cond( path[1] ), -1, -1, ""};
			insert_node(nodes, node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg );
		}
	}




}

Path put_nth(string cond, Path path, int depth){

	//printf("put_nth\n");
	//print_path(path);
	//printf("cond %s\n", cond.c_str());
	//printf("depth %d\n", depth);

	Path ret;

	int n = 0;
	for( vector<string>::iterator it = path.begin(); it != path.end(); it++,n++ ){
		if( n==depth )
			ret.push_back(cond);
		ret.push_back(*it);
	}

	if(depth == path.size())
		ret.push_back(cond);
	
	return ret;
}

PathAndAssign get_to_front(PathAndAssign path_and_assign, string cond_pos, int depth){

	//printf("get_to_front\n---");
	//print_path_assign(path_and_assign);
	//printf("cond_pos %s\n", cond_pos.c_str() );

	Path path = path_and_assign.path;
	string assign = path_and_assign.assign;

	Path path_without_cond;
	string cond;

	for( Path::iterator it = path.begin(); it != path.end(); it++ ){

		if( cond_pos == *it || cond_pos == negation(*it) ){
			cond = *it;
		} else {
			path_without_cond.push_back(*it);
		}
	}

	PathAndAssign path_and_assign_ret;
	path_and_assign_ret.path = put_nth(cond, path_without_cond, depth);
	path_and_assign_ret.assign = assign;

	//printf("\n+++");
	//print_path_assign(path_and_assign_ret);

	return path_and_assign_ret;
}

void get_to_front(vector<PathAndAssign>& path_and_assigns, string cond_pos, int depth){


	for ( unsigned int i = 0; i < path_and_assigns.size(); i++) {
		path_and_assigns[i] = get_to_front(path_and_assigns[i], cond_pos, depth);
	}
	
}

void make_tree(vector<Node>& nodes, vector<PathAndAssign> paths_and_assign, vector<string> cond_ordering , int depth = 0){

	if( paths_and_assign.size() == 1 ){
		add_path(nodes, paths_and_assign[0]);
		return;
	}

	for( vector<string>::iterator it = cond_ordering.begin(); it != cond_ordering.end(); it++ ){
		//printf("variable %s\n", it->c_str());
		if(is_complete(*it, paths_and_assign)){
			//printf("is_complete\n");
			vector<PathAndAssign> paths_pos;
			vector<PathAndAssign> paths_neg;
			part_paths(*it,paths_and_assign, paths_pos, paths_neg);

			get_to_front(paths_pos, *it, depth);
			get_to_front(paths_neg, *it, depth);

			assert(paths_pos.size() + paths_neg.size() == paths_and_assign.size());

			make_tree(nodes, paths_pos, remove(cond_ordering, *it) , depth + 1);
			make_tree(nodes, paths_neg, remove(cond_ordering, *it) , depth + 1);
		}
	}
	
}

set<string> get_set_variables(vector<PathAndAssign> path_and_assigns){

	set<string> ret;
	for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ ){
		Path path = it->path;
		for( vector<string>::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			string cond = *it2;
			if( cond.substr(0,5) == "(not ")
				ret.insert(negation(*it2));
			else
				ret.insert(*it2);
		}
	}

	return ret;
	
}

void permute(vector<string>& variables_vec){

	for ( unsigned int i = 0; i < cmd_option_int("bdd_permutation"); i++) {
		next_permutation(variables_vec.begin(), variables_vec.end());
	}

}

void normalize(PathAndAssign& path_and_assign){

	Path path = path_and_assign.path;

	for ( unsigned int i = 0; i < path.size(); i++) {
		string cond = path[i];

		while(cond.substr(0,10) == "(not (not "){
			string right = cond.substr(10);
			cond = right.substr(0,right.length()-2);
		}

		path[i] = cond;
	}
	
	path_and_assign.path = path;
}

void normalize(vector<PathAndAssign>& path_and_assigns){

	for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ )
		normalize(*it);
	
}



string get_ite_expr(vector<Node> nodes, int n = 0){
	Node node = nodes[n];
	if(node.node_pos == -1 || node.node_neg == -1)
		return (node.assign == "")?"0":node.assign;

	return string("(ite ") + " " + node.cond_pos + " " + get_ite_expr(nodes, node.node_pos) + " " + get_ite_expr(nodes, node.node_neg) + ")";
}

typedef struct ParentStruct {
	string branch;
	int node;
} ParentStruct;


vector<ParentStruct> get_parents(vector<Node> nodes, int n){

	vector<ParentStruct> ret;
	ParentStruct ps;

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].node_pos == n && nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "both";
			ret.push_back(ps);
		} else if(nodes[i].node_pos == n){
			ps.node = i;
			ps.branch = "pos";
			ret.push_back(ps);
		} else if(nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "neg";
			ret.push_back(ps);
		}
	}
	return ret;
}

void pass_1(vector<Node>& nodes){

	map<string, int> map_contents;
	set<string> set_contents;
	int num_nodes = nodes.size();

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].assign != "" && set_contents.find(nodes[i].assign) == set_contents.end() ){
			map_contents[ nodes[i].assign ] = num_nodes;
			set_contents.insert(nodes[i].assign);
			num_nodes++;
		}
	}

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].assign != ""){
			vector<ParentStruct> parents = get_parents(nodes, i);
			int node_dest = map_contents[ nodes[i].assign ];

			for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					nodes[it->node].node_pos = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					nodes[it->node].node_neg = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					nodes[it->node].node_pos = node_dest;
					nodes[it->node].node_neg = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				}
			}
		}
	}

	for( set<string>::iterator it = set_contents.begin(); it != set_contents.end(); it++ ){
		Node node = { "", -1, -1, *it};
		nodes.push_back(node);
	}
	

}

void pass_2(vector<Node>& nodes){
	//return;
	for ( unsigned int i = 0; i < nodes.size(); i++) {
	//unsigned int i = 19;{
		for ( unsigned int k = 0; k < nodes.size(); k++) {
		//unsigned int k = 11; {
			if(nodes[i].node_pos == nodes[k].node_pos && nodes[i].node_neg == nodes[k].node_neg){

				if(nodes[i].node_pos == -1 && nodes[i].node_neg == -1 ) continue;
				if(nodes[k].node_pos == -1 && nodes[k].node_neg == -1 ) continue;
				if( i == k ) continue;

				vector<ParentStruct> parents = get_parents(nodes, k);

				for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
					if(it->branch == "pos"){
						nodes[it->node].node_pos = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					} else if(it->branch == "neg"){
						nodes[it->node].node_neg = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					} else if(it->branch == "both"){
						nodes[it->node].node_pos = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					}
				}
				
			}
		}
	}

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( (nodes[i].node_pos == -1 && nodes[i].node_neg == -1) && nodes[i].cond_pos != ""){
			vector<ParentStruct> parents = get_parents(nodes, i);
			for ( unsigned int k = 0; k < parents.size(); k++) {
				int n = parents[k].node;
				nodes[n].assign = ""; nodes[n].node_pos = nodes[n].node_neg = -1;
			}
		}
	}
	
}

void pass_3(vector<Node>& nodes){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( nodes[i].node_pos == nodes[i].node_neg ){

			if(nodes[i].node_pos == -1) continue;

			vector<ParentStruct> parents = get_parents(nodes,i);
			int dest = nodes[i].node_pos;

			for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					nodes[it->node].node_pos = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					nodes[it->node].node_neg = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					nodes[it->node].node_pos = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				}
			}
		}
	}
}

void rm_invalid_nodes(vector<Node>& nodes){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( nodes[i].node_pos == -1 && nodes[i].node_neg == -1 && nodes[i].assign == "" ){
			nodes.erase(nodes.begin() + i);i--;
		}
	}
}

void robdd(vector<Node>& nodes){
	pass_1(nodes);
	pass_2(nodes);
	pass_3(nodes);
	//rm_invalid_nodes(nodes);
}


void get_model_fn(){

	vector<string> paths   = get_model_paths();
	vector<string> assigns = get_model_assigns();
	vector<string> names   = get_model_names();
	set<string>    free_v  = get_model_freevars();
	set<string>    outputs = get_model_outputs();

	assert(paths.size() == assigns.size());
	assert(paths.size() == names.size());

	stringstream model;
	model << "function:(define-fun gcd ( ";
	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		model << "(" << *it << " Int) ";
	}
	model << ") Int ";
	

	vector<PathAndAssign> path_and_assigns;

	//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(= main_register_b 0)"      ,  ","); pa.assign = "1"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(a),(not (b))"        ,  ","); pa.assign = "2"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(not (a)),(b)"        ,  ","); pa.assign = "3"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(not (a)),(not (b))"  ,  ","); pa.assign = "4"; path_and_assigns.push_back(pa); }
	
//{ PathAndAssign pa; pa.path = tokenize("(not (= main_register_a 0)),(not (= main_register_b 0))", ","); pa.assign = "0"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(not (= main_register_a 0)),(= main_register_b 0)", ","); pa.assign = "1"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(not (= main_register_b 0))", ","); pa.assign = "1"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(= main_register_b 0)", ","); pa.assign = "2"; path_and_assigns.push_back(pa);}
	
	
	
	for ( unsigned int i = 0; i < paths.size(); i++) {
		PathAndAssign pa;
		pa.path = tokenize(paths[i], ",");
		pa.assign = assigns[i];
		path_and_assigns.push_back(pa); 
	}

	normalize(path_and_assigns);

	//for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ ){
		//PathAndAssign path_and_assign = *it;
		//print_path_assign(path_and_assign);
	//}

	

	set<string> variables_set = get_set_variables(path_and_assigns);
	vector<string> variables_vec = vector<string>(variables_set.begin(), variables_set.end());

	//if(cmd_option_int("bdd_permutation"))
		//permute(variables_vec);

	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x3 0),(= main_register_x5 0),(= main_register_x7 0),(= main_register_x2 0),(= main_register_x4 0),(= main_register_x6 0),(= main_register_x8 0)", ",");
	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x2 0),(= main_register_x3 0),(= main_register_x4 0),(= main_register_x5 0),(= main_register_x6 0),(= main_register_x7 0),(= main_register_x8 0)", ",");
	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x2 0),(= main_register_x3 0)", ",");

	//for( vector<string>::iterator it = variables_vec.begin(); it != variables_vec.end(); it++ ){
		//printf("variable %s\n", it->c_str());
	//}
	
	
	vector<Node> nodes;
	make_tree(nodes, path_and_assigns, variables_vec);
	robdd(nodes);
	if(cmd_option_bool("show_bdd")) show_bdd(nodes);

	model << get_ite_expr(nodes);
	
	//exit(0);

	model << ")";


	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		printf("input:%s\n", it->c_str());
	}

	printf("%s\n", model.str().c_str());

}

int main(int argc, const char *argv[]) {


	load_default_options();
	set_current_path();

	if( argc >= 2 && argv[1][0] != '-' ){
		set_project_path( string(argv[1]) );
		load_file_options( string(argv[1]) );
	} else {
		set_project_path( current_path + "/config.xml" );
		load_file_options();
	}

	load_cmd_options(argc, argv);
	options_to_file();

	needs("test", "run");
	needs("final", "make_bc");
	needs("run", "final");
	needs("make_bc", "clean");
	needs("check_coverage", "measure_coverage");
	needs("compare_klee", "run");
	needs("compare_klee", "klee");
	needs("get_result", "test");
	needs("vim", "final");


	disables("compare_bc", "test");
	disables("compare_libs", "test");
	disables("make_bc", "test");
	disables("view_bc", "test");
	disables("view_bc", "check_coverage");
	disables("view_bc", "check_concurrency");
	disables("view_bc", "check_concurrency_2");
	disables("dfg", "test");
	disables("dfg", "check_coverage");
	disables("dfg2", "test");
	disables("dfg2", "check_coverage");
	disables("run", "test");
	disables("vim", "test");
	disables("show_results", "test");
	disables("show_results", "check_concurrency");
	disables("show_results", "check_concurrency_2");
	disables("show_results", "check_coverage");
	disables("show_test_vectors", "test");
	disables("show_test_vectors", "check_concurrency");
	disables("show_test_vectors", "check_concurrency_2");
	disables("show_test_vectors", "check_coverage");
	disables("show_argvs", "test");
	disables("show_argvs", "check_concurrency");
	disables("show_argvs", "check_concurrency_2");
	disables("show_argvs", "check_coverage");
	disables("count_branches", "test");
	disables("klee", "test");
	disables("klee", "compare_klee");
	disables("check_concurrency_2", "check_concurrency");
	disables("compare_bc", "test");
	disables("compare_bc", "check_concurrency");
	disables("compare_bc", "check_concurrency_2");
	disables("compare_bc", "check_coverage");
	disables("compare_measure_bc", "test");
	disables("compare_secuencialize", "test");
	disables("compare_secuencialize", "check_concurrency");
	disables("compare_secuencialize", "check_concurrency_2");
	disables("compare_klee", "test");
	disables("compare_klee", "check_coverage");
	disables("test_vectors", "test");
	disables("test_vectors", "compare_klee");
	disables("get_model", "test");
	disables("get_model_fn", "test");
	disables("get_static_heuristic", "test");
	disables("get_static_heuristic", "check_coverage");


	expand_options();


	//cmd_option_bool("verbose")
	//cmd_option_bool("see_each_problem")
	//cmd_option_bool("seq_name")
	//cmd_option_bool("with_libs")
	//cmd_option_bool("cyclotonic")
	//cmd_option_bool("unconstrained")
	//cmd_option_bool("dfg_function")
	//cmd_option_bool("show_only_constraints")
	//cmd_option_bool("show_bdd")
	//cmd_option_bool("bdd_permutation")
	if(cmd_option_bool("make_bc")) make_bc();
	if(cmd_option_bool("final")) final();
	if(cmd_option_bool("compare_bc")) compare_bc();
	if(cmd_option_bool("compare_measure_bc")) compare_measure_bc();
	if(cmd_option_bool("compare_libs")) compare_libs();
	if(cmd_option_bool("view_bc")) view_bc();
	if(cmd_option_bool("dfg")) view_dfg();
	if(cmd_option_bool("dfg2")) view_dfg_2();
	if(cmd_option_bool("run")) run();
	if(cmd_option_bool("test")) test();
	if(cmd_option_bool("show_results")) show_results();
	if(cmd_option_bool("show_argvs")) show_argvs();
	if(cmd_option_bool("show_test_vectors")) show_test_vectors();
	if(cmd_option_bool("measure_coverage")) measure_coverage();
	if(cmd_option_bool("test_vectors")) minimal_test_vectors_to_db();
	if(cmd_option_bool("show_coverage")) show_coverage();
	if(cmd_option_bool("check_coverage")) check_coverage();
	if(cmd_option_bool("random_testing")) random_testing();
	if(cmd_option_bool("count_branches")) count_branches();
	if(cmd_option_bool("klee")) do_klee();
	if(cmd_option_bool("clean_concurrency")) clean_concurrency();
	if(cmd_option_bool("concurrency")) extract_concurrency();
	if(cmd_option_bool("compare_concurrency")) compare_concurrency();
	if(cmd_option_bool("view_bc_concurrency")) view_bc_concurrency();
	if(cmd_option_bool("show_concurrency_table")) show_concurrency_table();
	if(cmd_option_bool("secuencialize")) secuencialize();
	if(cmd_option_bool("compare_secuencialize")) compare_secuencialize();
	if(cmd_option_bool("check_sync_tables")) check_sync_tables();
	if(cmd_option_bool("check_concurrency")) check_concurrency();
	if(cmd_option_bool("check_concurrency_2")) check_concurrency_2();
	if(cmd_option_bool("clean")) clean();
	if(cmd_option_bool("get_concurrent_functions")) get_concurrent_functions();
	if(cmd_option_bool("get_concurrent_info")) get_concurrent_info();
	if(cmd_option_bool("compare_klee")) compare_klee();
	if(cmd_option_bool("get_result")) get_result();
	if(cmd_option_bool("vim")) vim();
	if(cmd_option_bool("get_model")) get_model();
	if(cmd_option_bool("get_model_fn")) get_model_fn();
	if(cmd_option_bool("get_static_heuristic")) get_static_heuristic();

	return 0;

}

