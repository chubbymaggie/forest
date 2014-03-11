#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <string.h>
#include <sstream>
#include <set>
#include <map>
#include <assert.h>

using namespace std;

typedef struct Location{
	int row;
	int column;
} Location;

typedef struct Range {
	Location start;
	Location end;
} Range;


vector<Range> get_ranges(vector<string> names, string type){

	vector<Range> ret_v;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		//command << "cat ast | grep " << type << " | egrep '\\<" << *it << "\\>' | grep -v '/usr/'";
		command << "cat ast | egrep '" << type << " [^<]*<[^>]*> " << *it << "($| .*)'";
		command << " | grep -v '/usr/'";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 512 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));

		}
		fclose ( file );

		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s %s\n", it->c_str(), type.c_str());
			assert(0);
		}

		command.str("");
		

		FILE *fp;
		char ret[128];
		//command << "cat /tmp/ast_filter | sed 's/[^:]*:\([^:]*\):\([^,]*\),[^:]*:\([^:]*\):\([^>]*\)>.*/\1 \2 \3 \4/g'";
		command << "cat /tmp/ast_filter | sed 's/[^:]*:\\([^:]*\\):\\([^,]*\\),[^:]*:\\([^:]*\\):\\([^>]*\\)>.*/\\1 \\2 \\3 \\4/g'";
		
		int r1, c1, r2, c2;
		fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d %d %d %d", &r1, &c1, &r2, &c2);
		pclose(fp);

		//printf("%d %d %d %d\n", r1, c1, r2, c2);


		Location start = {r1, c1};
		Location end = {r2, c2};
		Range range = {start, end};
		ret_v.push_back(range);
		
		
	}

	return ret_v;
	
}


vector<Range> get_ranges_globals(vector<string> names, string type){

	vector<Range> ret_v;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		//command << "cat ast | grep " << type << " | egrep '\\<" << *it << "\\>' | grep -v '/usr/'";
		command << "cat ast | egrep '" << type << " [^<]*<[^>]*> " << *it << "($| .*)'";
		command << " | grep -v '/usr/'";
		command << " | grep -v 'extern'";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 512 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));

		}
		fclose ( file );

		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s %s\n", it->c_str(), type.c_str());
			assert(0);
		}

		command.str("");
		

		FILE *fp;
		char ret[128];
		//command << "cat /tmp/ast_filter | sed 's/[^:]*:\([^:]*\):\([^,]*\),[^:]*:\([^:]*\):\([^>]*\)>.*/\1 \2 \3 \4/g'";
		command << "cat /tmp/ast_filter | sed 's/[^:]*:\\([^:]*\\):.*/\\1/g'";

		int r1, c1, r2, c2;
		fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d %d %d %d", &r1, &c1, &r2, &c2);
		pclose(fp);

		//printf("%d %d %d %d\n", r1, c1, r2, c2);


		Location start = {r1, 0};
		Location end = {r1, 0};
		Range range = {start, end};
		ret_v.push_back(range);
		
		
	}

	return ret_v;
	
}


void out_line(int count, string line_s, vector<Range> ranges, bool whole_line){

	bool start = false;
	bool middle = false;
	bool end = false;
	int column;


	for( vector<Range>::iterator it = ranges.begin(); it != ranges.end(); it++ ){
		if( it->start.row == count ){ start = true; column = it->start.column; break; }
		else if( it->start.row < count && count < it->end.row ) { middle = true; break; }
		else if( it->end.row == count ) { end = true; column = it->end.column; break;}
	}

	//printf("out_line %d %d %d %d %d\n", count, start, middle, end, ranges.size());

	if(whole_line){
		if(start) printf("%s\n", line_s.c_str() );
		else if(middle) printf("%s\n", line_s.c_str() );
		else if(end) printf("%s\n\n", line_s.c_str() );
	} else {
		if(start) printf("%s\n", line_s.substr(column-1).c_str() );
		else if(middle) printf("%s\n", line_s.c_str() );
		else if(end) printf("%s\n\n", line_s.substr(0, column).c_str() );
	}

	
	
}

void output_range(vector<Range> ranges, bool whole_line){

	FILE *file = fopen ( "/tmp/std_files.c", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	string line_s;

	int count = 0;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		line_s = string(line);
		count++;


		out_line(count, line_s, ranges, whole_line);


	}
	fclose ( file );
	

}

void generate_ast(){

	FILE *file = fopen ( "files", "r" );
	char line [ 128 ]; // or other suitable maximum line size
	vector<string> files;

	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		files.push_back(string(line));
	}
	fclose ( file );

	stringstream command;
	command << "cat";
	for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
		command << " " << *it;
	}
	command << "> /tmp/std_files.c";
	system(command.str().c_str());

	vector<string> defines;
	defines.push_back("errno");


	command.str("");
	command << "cd /tmp/;";
	command << "clang -Xclang -ast-dump -fno-color-diagnostics ";

	for( vector<string>::iterator it = defines.begin(); it != defines.end(); it++ ){
		command << "-D" << *it << " ";
	}


	command << " std_files.c > ast 2>/dev/null";
	system(command.str().c_str());


	command.str("");
	command << "sed -i s/__xpg_basename/basename/g /tmp/ast";
	system(command.str().c_str());

}

vector<string> get_names(string filename){

	vector<string> ret;

	FILE *file = fopen ( filename.c_str(), "r" );
	char line [ 128 ]; // or other suitable maximum line size

	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		if(line[0] != '#' && line != "")
			ret.push_back(string(line));
	}
	fclose ( file );

	return ret;
}

map<string, string> get_typedefs(vector<string> names){

	map<string, string> ret_m;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat ast | egrep 'TypedefDecl [^<]*<[^>]*> " << *it << " .*' | cut -d\"'\" -f2";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));
		}
		fclose ( file );

		
		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s\n", it->c_str());
			assert(0);
		}

		ret_m[*it] = lines[0];

	}

	return ret_m;
	
}

void output_typedefs_2(map<string, string> typedefs){
	for( map<string,string>::iterator it = typedefs.begin(); it != typedefs.end(); it++ ){
		printf("typedef %s %s;\n", it->second.c_str(), it->first.c_str() );
	}
	
}



map<string, string> get_externs(vector<string> names){

	map<string, string> ret_m;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat ast | egrep 'VarDecl [^<]*<[^>]*> " << *it << " .*' | cut -d\"'\" -f2";
		command << " | sort | uniq ";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));
		}
		fclose ( file );

		
		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s\n", it->c_str());
			assert(0);
		}

		ret_m[*it] = lines[0];

	}

	return ret_m;
	
}

vector<string> get_decls(vector<string> names){

	vector<string> ret_v;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat ast | egrep 'FunctionDecl [^<]*<[^>]*> " << *it << " .*' | cut -d\"'\" -f2";
		command << " | sort | uniq ";
		command << " | sed 's/\\([^(]*\\)\\((.*\\)/\\1 " << *it << " \\2;/g' ";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));
		}
		fclose ( file );

		
		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s\n", it->c_str());
			assert(0);
		}

		ret_v.push_back(lines[0]);

	}

	return ret_v;
	
}



vector<string> get_defines(vector<string> names){

	vector<string> ret_v;

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat std_files.c | grep '#define[\t ]*" << *it << "[\t ]*.*'";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));
		}
		fclose ( file );

		
		if(lines.size() != 1){
			fprintf(stderr, "Multiple or zero definitions of %s\n", it->c_str());
			assert(0);
		}

		ret_v.push_back(lines[0]);

	}

	return ret_v;
	
}

void output_defines(vector<string> defines){


	for( vector<string>::iterator it = defines.begin(); it != defines.end(); it++ ){
		printf("%s\n", it->c_str() );
	}
	
}

void output_externs(map<string, string> externs){

	for( map<string,string>::iterator it = externs.begin(); it != externs.end(); it++ ){
		printf("%s %s;\n", it->second.c_str(), it->first.c_str());
	}
	
}

void output_decls(vector<string> decls){
	for( vector<string>::iterator it = decls.begin(); it != decls.end(); it++ ){
		printf("%s\n", it->c_str());
	}
	
}

void output_add(string filename){

	FILE *file = fopen ( filename.c_str(), "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		fputs ( line, stdout );
		printf("\n");
	}
	fclose ( file );
	
}

void compile(){
	stringstream command;
	command << "llvm-g++ --emit-llvm salida.cpp 2>&1 | grep error";
	system(command.str().c_str());
}

int main() {

	generate_ast();

	printf("/* defines */\n\n");
	vector<string> defines_to_extract = get_names("defines");
	vector<string> defines = get_defines(defines_to_extract);
	output_defines(defines);

	printf("/* typedefs */\n\n");
	vector<string> typedefs_to_extract = get_names("typedefs");
	vector<Range>  typedefs = get_ranges( typedefs_to_extract, "TypedefDecl");
	output_range(typedefs, true);

	vector<string> typedefs_to_extract_2 = get_names("typedefs_2");
	map<string, string> typedefs_2 = get_typedefs(typedefs_to_extract_2);
	output_typedefs_2(typedefs_2);

	printf("/* globals */\n\n");
	vector<string> globals_to_extract = get_names("globals");
	vector<Range>  globals = get_ranges_globals( globals_to_extract, "VarDecl");
	output_range(globals, true);

	printf("/* decls */\n\n");
	vector<string> decls_to_extract = get_names("decls");
	vector<string> decls = get_decls(decls_to_extract);
	output_decls(decls);


	printf("/* structs */\n\n");
	vector<string> structs_to_extract = get_names("structs");
	vector<Range>  structs = get_ranges( structs_to_extract, "RecordDecl");
	output_range(structs,true);

	printf("/* enums */\n\n");
	vector<string> enums_to_extract = get_names("enums");
	vector<Range>  enums = get_ranges( enums_to_extract, "TypedefDecl");
	output_range(enums , true);

	printf("/* externs */\n\n");
	vector<string> externs_to_extract = get_names("extern");
	map<string, string> externs = get_externs( externs_to_extract);
	output_externs(externs);


	printf("/* functions */\n\n");
	output_add("extra_functions.c");
	vector<string> funcs_to_extract = get_names("functions");
	vector<Range> functions = get_ranges(funcs_to_extract, "FunctionDecl");
	output_range(functions, false);



	//compile();




	return 0;
}
