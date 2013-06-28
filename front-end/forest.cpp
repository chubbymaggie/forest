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
#include <set>

#define SIZE_STR 512

#define debug true

using namespace std;

bool done_bc = false;
bool done_final = false;
bool done_run = false;

typedef struct VarLocation {
	string name;
	string type;
	int line;
} VarLocation;


std::map<std::string, std::string> options; // Opciones del fichero XML / linea de comandos

map<string, VarLocation > variable_locations;
int main_line;

string cd_path;

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

void load_variable_location(string file){

	printf("load_variable_location\n"); fflush(stdout);

	variable_locations.clear();

	TiXmlDocument doc(file.c_str()); // documento xml
	doc.LoadFile();
	
	std::string m_name; // nombre
	
	TiXmlHandle hDoc(&doc); // handler del xml
	TiXmlElement* pElem; // cada elemento
	TiXmlHandle hRoot(0); // raiz del xml
	
	pElem=hDoc.FirstChildElement("variables").Element();
	m_name=pElem->Value();
	
	hRoot=TiXmlHandle(pElem);

	pElem=hRoot.FirstChild().Element();
	for( ; pElem; pElem=pElem->NextSiblingElement()){

		printf("%s %s %s\n", pElem->Attribute("name"), pElem->Attribute("type"), pElem->Attribute("line"));

		string name_hint = pElem->Attribute("name_hint");
		string name      = pElem->Attribute("name");
		string type      = pElem->Attribute("type");
		string line_s    = pElem->Attribute("line"); int line; sscanf(line_s.c_str(), "%d", &line);

		VarLocation vl = {name, type, line};

 		variable_locations[name_hint] = vl;


	}


	pElem=hDoc.FirstChildElement("main").Element();
	m_name=pElem->Value();
	
	hRoot=TiXmlHandle(pElem);

	pElem=hRoot.FirstChild().Element();
	for( ; pElem; pElem=pElem->NextSiblingElement()){

		//printf("%s\n", pElem->Attribute("line"));
		sscanf(pElem->Attribute("line"), "%d", &main_line);

	}



	
}

void load_default_options(string file){

	options.clear();

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
	load_default_options(string("config.xml"));
}

void cmd_option_set(string key, string value ){

	options[key] = value;


}

void systm( string cmd ){

	if( cmd_option_bool("verbose") )
		printf("\e[31m %s \e[0m\n", cmd.c_str() );

	stringstream command;

	if( cd_path != "" ){
		command << "cd " << cd_path << ";";
	}
	
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
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < /tmp/file.bc > /tmp/file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < /tmp/file-2.bc > /tmp/file-3.bc";
	systm(cmd.str().c_str());

	done_bc = true;

}

void compare_bc(){


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

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
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < /tmp/file.bc > /tmp/file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < /tmp/file-2.bc > /tmp/salida1.txt";
	systm(cmd.str().c_str());


	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < /tmp/file-2.bc > /tmp/file-3.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < /tmp/file-3.bc > /tmp/salida2.txt";
	systm(cmd.str().c_str());


	// Comparación
	cmd.str("");
	cmd << "meld /tmp/salida1.txt /tmp/salida2.txt";
	systm(cmd.str().c_str());



}

void compare_measure_bc(){


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

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
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < /tmp/file.bc > /tmp/file-2.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < /tmp/file-2.bc > /tmp/salida1.txt";
	systm(cmd.str().c_str());


	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < /tmp/file-2.bc > /tmp/file-3.bc";
	systm(cmd.str().c_str());

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < /tmp/file-3.bc > /tmp/salida2.txt";
	systm(cmd.str().c_str());


	// Comparación
	cmd.str("");
	cmd << "meld /tmp/salida1.txt /tmp/salida2.txt";
	systm(cmd.str().c_str());



}

void view_bc(){

	stringstream cmd;

	// Desensamblado
	cmd.str("");
	cmd << "llvm-dis < /tmp/file-2.bc > /tmp/salida1.txt";
	systm(cmd.str().c_str());

	// Visualizar
	cmd.str("");
	cmd << "gedit /tmp/salida1.txt &";
	systm(cmd.str().c_str());

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

	// linka
	cmd.str("");
	cmd << "g++ /tmp/file-3.o " << base_path << "/lib/forest.a" << " -lpthread -ldl -o " << output_file;
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


	cmd.str("");
	if( cd_path != "" ){
		cmd << "cd " << cd_path << ";";
	}
	cmd << "diff results gold_result > /dev/null";
	int result = system(cmd.str().c_str());

	if( result )
		printf("\e[31m Failed :( \e[0m\n");
	else
		printf("\e[32m Passed :) \e[0m\n");

}

void set_path( string file ){

	vector<string> tokens = tokenize(file, "/");

	string path_aux;

	for ( unsigned int i = 0; i < tokens.size() - 1; i++) {
		path_aux += tokens[i] + "/";
	}

	cd_path = path_aux;
	

}

void view_dfg(){


	stringstream cmd;

	// Crea el bc
	cmd.str("");
	cmd << "llvm-gcc --emit-llvm -c " << cmd_option_string_vector("file")[0] << "-o /tmp/file.bc";
	systm(cmd.str().c_str());

	// paso de optimización dot
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "opt -dot-cfg < /tmp/file.bc 2>&1 | grep Writing";
	
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

	printf("\e[31m coversbool \e[0m\n");
	for( vector<string>::iterator it = v1.begin(); it != v1.end(); it++ ){
		printf("%s ", it->c_str() );
	}
	printf(" -- ");
	for( vector<string>::iterator it = v2.begin(); it != v2.end(); it++ ){
		printf("%s ", it->c_str() );
	}
	
	
	for ( unsigned int i = 0; i < v1.size(); i++) {
		//printf("%s %s ", v1[i].c_str(), v2[i].c_str() );
		if( v1[i] != v2[i] && v1[i] != "X" && v2[i] != "X" ){
			printf("not cover\n"); //getchar();
			return false;
		}
	}

	printf("cover\n"); //getchar();

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
	command << "echo 'select name,value,problem_id from results where is_free;' | sqlite3 database.db";
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

	for ( unsigned int i = 0; i < 4; i++) {
		
	set<vector<string> > to_insert;
	set<vector<string> > to_remove;

		printf("\e[31m Prunning iteration \e[0m\n");








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
					printf("\e[34m Insert nodc \e[0m"); printvector( *v1 );
					to_insert.insert(*v1);
				}

				bool someonecovers = false;
				if( dontcares(*v1) || dontcares(*v2) ){

					printf("\e[31m v1 \e[0m "); printvector(*v1);
					printf("\e[31m v2 \e[0m "); printvector(*v2);

					if( covers_bool(*v1, *v2) ){
						someonecovers = true;
						to_remove.insert(*v1); printf("\e[34m remove \e[0m "); printvector(*v1);
						to_remove.insert(*v2); printf("\e[34m remove \e[0m "); printvector(*v2);
						printf("\e[34m Insert  \e[0m"); printvector( covers(*v1, *v2) );
						to_insert.insert( covers(*v1, *v2) );
					}

					printf("someone covers %d\n", someonecovers);

					//if( !someonecovers ){
						//printf("\e[34m noone covers  \e[0m"); printvector(*v1);
						//to_insert.insert(*v1);
					//}

				}

			}

		}

		printf("values_set.size() %lu\n", values_set.size());
		printf("toremove.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_remove.begin(); it != to_remove.end(); it++ ){
			printf("remove "); printvector(*it);
			values_set.erase( values_set.find(*it) );
		}

		printf("toinsert.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_insert.begin(); it != to_insert.end(); it++ ){
			printf("insert "); printvector(*it);
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

	}


	

	return values_set;
	
}


void gen_file_free_variables(){


	stringstream cmd;

	cmd.str("");
	cmd << "echo 'select name,type,position from variables group by name;' | sqlite3 database.db";

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret) - 1 ] = 0;
		ret_vector.push_back(ret);

	}
	
	pclose(fp);

	vector<string> outfile;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		outfile.push_back( tokens[0] + " " + tokens[1] + " " + tokens[2]);
	}

	FILE* file = fopen("free_variables", "w");
	for( vector<string>::iterator it = outfile.begin(); it != outfile.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
	
	

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



	FILE* file = fopen("vectors", "w");
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
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < /tmp/file.bc > /tmp/file-2.bc";
	systm(cmd.str().c_str());

	// Segundo paso de optimización
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < /tmp/file-2.bc > /tmp/file-3.bc";
	systm(cmd.str().c_str());

	// Pasa de .bc a .s
	cmd.str("");
	cmd << "llc /tmp/file-3.bc -o /tmp/file-3.s";
	systm(cmd.str().c_str());

	// Pasa de .s a .o
	cmd.str("");
	cmd << "gcc -c /tmp/file-3.s -o /tmp/file-3.o";
	systm(cmd.str().c_str());

	// linka
	cmd.str("");
	cmd << "g++ /tmp/file-3.o " << base_path << "/lib/measurement.a -lpthread -ldl -o " << output_file;
	systm(cmd.str().c_str());

}


//void gen_test_prg(){

	//pair<set<string>, set<vector<string> > > min_vects = minimal_vectors();

	//set<string> names = min_vects.first;
	//set<vector<string> > values = min_vects.second;



	//FILE *file = fopen ( cmd_option_str("file").c_str(), "r" );
	//char line [ 128 ]; [> or other suitable maximum line size <]
	//vector<string> file_vector;
	
	//while ( fgets ( line, sizeof(line), file ) != NULL ){
		//line[strlen(line)-1] = 0;
		//file_vector.push_back( string(line) );
	//}
	//fclose ( file );
	
	
	//load_variable_location("config.xml");

	//for( map<string,VarLocation>::iterator it = variable_locations.begin(); it != variable_locations.end(); it++ ){

		//string name_hint = it->first;
		//string name      = it->second.name;
		//string type      = it->second.type;
		//int line         = it->second.line;

		//file_vector[line-1] = type + " " + name + " = " + "register_" + name + ";";

	//}

	//file_vector[main_line-1] = "void test(void){";
	



	//vector<string> main_and_global;

	//for( set<string>::iterator it = names.begin(); it != names.end(); it++ ){
		//main_and_global.push_back("int " + *it + ";");
	//}
	
	//main_and_global.push_back( "" );
	//main_and_global.push_back( "int main(){" );
	//main_and_global.push_back( "" );

	//for( set<vector<string> >::iterator it = values.begin(); it != values.end(); it++ ){
		//vector<string> vect = *it;

		//set<string>::iterator name = names.begin();
		//vector<string>::iterator value = vect.begin();

		//for( ; name != names.end(); name++,value++ ){
			//main_and_global.push_back( "\t" + *name + " = " + *value + ";" );
		//}

		//main_and_global.push_back( "\ttest();" );
		//main_and_global.push_back( "" );

	//}


	//main_and_global.push_back( "}" );
	//main_and_global.push_back( "" );
	

	//int lineinsert = main_line - 1;	

	//for( vector<string>::iterator it = main_and_global.begin(); it != main_and_global.end(); it++,lineinsert++ ){
		////file_vector.insert(file_vector.begin() + main_line - 1, *it );
		//file_vector.insert(file_vector.begin() + lineinsert, *it );
		
	//}
	

	////for( vector<string>::iterator it = main_and_global.begin(); it != main_and_global.end(); it++ ){
		////printf("%s\n", it->c_str());
	////}
	

	//for( vector<string>::iterator it = file_vector.begin(); it != file_vector.end(); it++ ){
		//printf("%s\n", it->c_str());
	//}
	



//}

void measure_coverage(){

	gen_file_free_variables();
	gen_file_vectors();
	gen_final_for_measurement();


	// Ejecuta
	
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" + output_file;
	systm(cmd.str().c_str());
	

}

int main(int argc, const char *argv[]) {

	if( argc >= 2 && argv[1][0] != '-' ){
		load_default_options( string(argv[1]) );
		set_path( string(argv[1]) );
	} else {
		load_default_options();
	}

	parse_cmd_line(argc, argv);

	if( cmd_option_bool("test") ){
		set_option("run", "true");
	}

	set_option("developer", "true");

	if(cmd_option_bool("make_bc")) make_bc();
	if(cmd_option_bool("final")) final();
	if(cmd_option_bool("compare_bc")) compare_bc();
	if(cmd_option_bool("compare_measure_bc")) compare_measure_bc();
	if(cmd_option_bool("view_bc")) view_bc();
	if(cmd_option_bool("dfg")) view_dfg();
	if(cmd_option_bool("run")) run();
	if(cmd_option_bool("test")) test();
	if(cmd_option_bool("show_results")) show_results();
	//if(cmd_option_bool("gen_test")) gen_test_prg();
	if(cmd_option_bool("measure_coverage")) measure_coverage();


	return 0;
}

