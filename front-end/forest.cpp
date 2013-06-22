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
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include "./tinyxml.h"
#include <string>
#include <sstream>
#include <vector>
#include <map>

#define SIZE_STR 512

using namespace std;

bool done_bc = false;
bool done_final = false;
bool done_run = false;

std::map<std::string, std::string> options; // Opciones del fichero XML / linea de comandos

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

void parse_cmd_line(int argc, const char** argv ){
	
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
	return options[option];
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

void load_default_options(){
	
	options.clear();

	TiXmlDocument doc("config.xml"); // documento xml
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

void cmd_option_set(string key, string value ){

	options[key] = value;


}

void systm( string cmd ){

	if( cmd_option_bool("verbose") )
		printf("\e[31m %s \e[0m\n", cmd.c_str() );

	stringstream command;
	
	if( cmd_option_bool("verbose") )
		command << cmd;
	else
		command << "(" << cmd << ") >/dev/null 2>/dev/null";

	system(command.str().c_str() );
}

void make_bc(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	// Copiar el paso a la carpeta
	cmd.str("");
	cmd << "sudo cp " << base_path << "/optim-pass/optimization_pass.cpp " << llvm_path << "/lib/Transforms/Hello/Hello.cpp";
	systm(cmd.str().c_str());

	// make del paso de optimización
	cmd.str("");
	cmd << "sudo make -C " << llvm_path << "/lib/Transforms/Hello/";
	systm(cmd.str().c_str());

	// Junta todos los .c en uno
	cmd.str("");
	cmd << "cat ";
	vector<string> files = cmd_option_string_vector("file");
	for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
		cmd << *it << " ";
	}
	cmd << "> /tmp/file.cpp";
	systm(cmd.str().c_str());
	
	// Compilación del código a .bc
	cmd.str("");
	cmd << "llvm-gcc -O0 --emit-llvm -c /tmp/file.cpp -o /tmp/file.bc";
	systm(cmd.str().c_str());

	// Primer paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/LLVMHello.so -fill_names < /tmp/file.bc > /tmp/file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/LLVMHello.so -all < /tmp/file-2.bc > /tmp/file-3.bc";
	systm(cmd.str().c_str());

	done_bc = true;

}

void compare_bc(){

}

void view_bc(){

}

void final(){

	if( !done_bc ) make_bc();

	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	stringstream cmd;

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc /tmp/file-3.bc -o /tmp/file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c /tmp/file-3.s -o /tmp/file-3.o";
	systm(cmd.str().c_str());

	// Compila el back-end
	cmd.str("");
	cmd << "g++ -g -c "  << base_path << "/back-end/operators.cpp -o /tmp/operators.o;";
	cmd << "g++ -g -c "  << base_path << "/back-end/solver.cpp -o /tmp/solver.o;";
	cmd << "g++ -g -c "  << base_path << "/back-end/database.cpp -o /tmp/database.o;";
	cmd << "gcc -c "     << base_path << "/back-end/sqlite3.c -o /tmp/sqlite3.o;";
	cmd << "g++ /tmp/file-3.o /tmp/operators.o /tmp/solver.o /tmp/sqlite3.o /tmp/database.o -lpthread -ldl -o " << output_file;
	systm(cmd.str().c_str());

	done_final = true;
}

void run(){

	if( !done_final ) final();

	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	stringstream cmd;

	// Ejecuta el fichero resultante
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());

	done_run = true;

}

void show_results(){

	//if( !done_run ) run();

	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd.str("");
	cmd << "echo '.mode columns\\n.width 20 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;' | sqlite3 database.db";



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


	string explanation = cmd_option_str("explanation") + " ";

	while( explanation.length() < 50 )
		explanation = explanation + ".";

	printf("* Testing %s", explanation.c_str() );

	stringstream cmd;

	// Muestro los resultados de la base de datos
	cmd.str("");
	cmd << "echo '.mode columns\\n.width 20 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;'";
	cmd << " | sqlite3 database.db ";
	cmd << "> results";
	systm(cmd.str().c_str());


	int result = system("diff results gold_result > /dev/null");

	if( result )
		printf("\e[31m Failed :( \e[0m\n");
	else
		printf("\e[32m Passed :) \e[0m\n");

}

int main(int argc, const char *argv[]) {
	load_default_options();
	parse_cmd_line(argc, argv);
	
	if(cmd_option_bool("make_bc")) make_bc();
	if(cmd_option_bool("final")) final();
	if(cmd_option_bool("compare_bc")) compare_bc();
	if(cmd_option_bool("view_bc")) view_bc();
	if(cmd_option_bool("run")) run();
	if(cmd_option_bool("test")) test();
	if(cmd_option_bool("show_results")) show_results();

	return 0;
}
