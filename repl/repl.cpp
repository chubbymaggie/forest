#include <panel.h>
#include <string.h>
#include <vector>
#include <string>
#include <assert.h>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <stdlib.h>

using namespace std;

void init_wins(WINDOW **wins, int n);
void win_show_title(WINDOW *win, char *label);
void win_show_box(WINDOW *win);
void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string, chtype color);

typedef struct Model {
	string content;
	string name;
	vector<string> inputs;
	vector<string> outputs;
} Model;

typedef struct Assign {
	string name;
	string input_output;
	string value;
} Assign;

WINDOW *wins[4];            // Windows
PANEL  *my_panels[4];       // Panels
PANEL  *top;                // Top panel
int ch;                     // Character type 
char command[128];          // repl command_prompt 
int len_command;            // command length
vector<string> buffer_0;    // buffer of windows 0
vector<string> buffer_1;    // buffer of windows 1
vector<string> buffer_2;    // buffer of windows 2
vector<Model>  models;      // Models
vector<string> assumptions; // Assumptions
vector<Assign> assigns;     // Counter-Example solution



void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}


void initialize(){
	/* Initialize curses */
	initscr();
	start_color();

	/* Initialize all the colors */
	init_pair(1, COLOR_BLUE, COLOR_BLACK);
	init_pair(2, COLOR_MAGENTA, COLOR_BLACK);
	init_pair(3, COLOR_GREEN, COLOR_BLACK);
	init_pair(4, COLOR_RED, COLOR_BLACK);
}

void initialize_panels(){

	/* Attach a panel to each window */
	my_panels[0] = new_panel(wins[0]);
	my_panels[1] = new_panel(wins[1]);
	my_panels[2] = new_panel(wins[2]);
	my_panels[3] = new_panel(wins[3]);

	/* Set up the user pointers to the next panel */
	set_panel_userptr(my_panels[0], my_panels[1]);
	set_panel_userptr(my_panels[1], my_panels[2]);
	set_panel_userptr(my_panels[2], my_panels[3]);
	set_panel_userptr(my_panels[3], my_panels[0]);
}

void initialize_wins() {
	int x, y, i;
	char label[80];

	wins[0] = newwin(LINES-5      , COLS*3/4, 0          , 0)        ; win_show_box  (wins[0]) ;
	wins[1] = newwin((LINES-5)/2  , COLS*1/4, 0          , COLS*3/4) ; win_show_title(wins[1], (char*)"Variables") ;
	wins[2] = newwin((LINES-5)/2+1, COLS*1/4, (LINES-5)/2, COLS*3/4) ; win_show_title(wins[2], (char*)"Counter Example") ;
	wins[3] = newwin(5            , COLS    , LINES-5    , 0)        ; win_show_box  (wins[3]) ;

	buffer_0.push_back("  Forest Read-Eval-Print-Loop ");
	buffer_0.push_back(" `-. .------------------------");
	buffer_0.push_back("    Y                         ");
	buffer_0.push_back("    ,,  ,---,                 ");
	buffer_0.push_back("   (_,\\/_\\_/_\\             ");
	buffer_0.push_back("     \\.\\_/_\\_/>            ");
	buffer_0.push_back("     '-'   '-'                ");
	buffer_0.push_back("                              ");
	buffer_0.push_back("                              ");

 
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



void mvwprintw_col(WINDOW* win, int row, int col, string line){

	int col_2 = 0;

	vector<string> tokens = tokenize(line, "#");

	if(tokens.size() > 1){

		for ( unsigned int i = 0; i < tokens.size(); i++) {
			if( tokens[i] == "magenta"){
				wattron(win, COLOR_PAIR(2));
			} else if(tokens[i] == "green"){
				wattron(win, COLOR_PAIR(3));
			} else if(tokens[i] == "red"){
				wattron(win, COLOR_PAIR(4));
			} else if(tokens[i] == "normal"){
				wattroff(win, COLOR_PAIR(1));
			} else {
				mvwprintw(win, row, col+col_2, "%s", tokens[i].c_str());
				col_2 += tokens[i].length();
			}

		}

	} else {
		mvwprintw(win, row, col, line.c_str());
	}
	

}

void draw_win_0(){


	for ( unsigned int row = 2; row < LINES-6; row++) {
		for ( unsigned int col = 2; col < COLS*3/4-3; col++) {
			mvwprintw(wins[0], row,col, " ");
		}
	}

	if(buffer_0.size() < LINES-8){
		for ( unsigned int i = 0; i < buffer_0.size(); i++) {
			mvwprintw_col(wins[0], i+2, 2, buffer_0[i].c_str());
		}

	} else {
		for ( unsigned int i = buffer_0.size()-(LINES-8),m=0; i < buffer_0.size(); i++,m++) {
			mvwprintw_col(wins[0], m+2, 2, buffer_0[i].c_str());
		}

	}
}

void draw_win_1(){

	buffer_1.clear();

	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		string name = it->name;
		buffer_1.push_back( "#magenta#" + name + "#normal#");
		vector<string> outputs = it->outputs;
		for( vector<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){
			buffer_1.push_back( " - #red#" + (*it) + "#normal#");
		}
		
	}

	set<string> inputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> inputs = it->inputs;
		for( vector<string>::iterator it2 = inputs.begin(); it2 != inputs.end(); it2++ ){
			string input = *it2;
			inputs_set.insert(input);
		}
	}

	for( set<string>::iterator it = inputs_set.begin(); it != inputs_set.end(); it++ ){
		buffer_1.push_back( "#green#" + (*it) + "#normal#");
	}

	for( vector<string>::iterator it = assumptions.begin(); it != assumptions.end(); it++ ){
		buffer_1.push_back("#magenta#" + (*it) + "#normal#");
	}
	
	
	

	for ( unsigned int row = 3; row < (LINES-5)/2-1; row++) {
		for ( unsigned int col = 1; col < COLS*1/4-1; col++) {
			mvwprintw(wins[1], row,col, " ");
		}
	}

	for ( unsigned int i = 0; i < buffer_1.size(); i++) {
		char line[512];
		sprintf(line, "%s", buffer_1[i].c_str());
		mvwprintw_col(wins[1], i+3, 2, line);
	}

}


void draw_win_2(){

	for ( unsigned int row = 3; row < (LINES-5)/2-1; row++) {
		for ( unsigned int col = 1; col < COLS*1/4-1; col++) {
			mvwprintw(wins[2], row,col, " ");
		}
	}

	buffer_2.clear();

	for( vector<Assign>::iterator it = assigns.begin(); it != assigns.end(); it++ ){
		buffer_2.push_back( ((it->input_output == "input")?"#green#":"#red#") + it->name + " = " + it->value + "#normal#");
	}
	

	if(buffer_2.size() < (LINES-5)/2-1 ){
		for ( unsigned int i = 0; i < buffer_2.size(); i++) {
			mvwprintw_col(wins[2], i+3, 1, buffer_2[i].c_str());
		}

	} else {

	}


}


string highlight(string command){
	string ret = command;
	myReplace(ret, "#green#", "");
	myReplace(ret, "import", "#green#import#normal#");
	myReplace(ret, "as", "#green#as#normal#");
	myReplace(ret, "check", "#green#check#normal#");
	return ret;
}

void draw_win_3(){

	for ( unsigned int row = 1; row < 4; row++) {
		for ( unsigned int col = 1; col < COLS-1; col++) {
			mvwprintw(wins[3], row,col, " ");
		}
	}

	string command_high = highlight(command);

	mvwprintw_col(wins[3], 2, 2, ">>> ");
	mvwprintw_col(wins[3], 2, 6, command_high);

	move(LINES-3, 6+len_command);
}

void complete_command(){

	string remaining = "";
	vector<string> tokens = tokenize(string(command), " ");
	if(!tokens.size()) return;

	if(tokens.size() == 1){

		vector<string> keys;
		keys.push_back("import");
		keys.push_back("check");

		for( vector<string>::iterator it = keys.begin(); it != keys.end(); it++ ){
			if(it->length() < len_command) continue;
			if(it->substr(0, len_command) == tokens[0])
				remaining = it->substr(len_command);
		}


	}

	strcat(command, remaining.c_str());
	len_command = strlen(command);
}

void update(){

	/* Update the stacking order. 2nd panel will be on top */
	update_panels();

	/* Show it on the screen */
	doupdate();

	refresh();

}

void command_prompt(int ch){
	mvwprintw(wins[0], 2, 2, "%d", ch);
	char chs[] = {ch, 0};
	strcat(command, chs);
	len_command++;
}

void begin_prompt(){

	strcpy(command, "");
	len_command = 0;
}

void finish(){
	endwin();
}


void import_model(string command_str){


	vector<string> tokens = tokenize(command_str, " ");
	assert(tokens[0] == "import");
	assert(tokens[1][0] == '/');
	assert(tokens[2] == "as");

	string file = tokens[1];
	string name = tokens[3];

	ifstream input(tokens[1].c_str());
	string line;
	
	vector<string> inputs;
	vector<string> outputs;


	buffer_0.push_back("#green#import#normal# " + tokens[1] + " #green#as#normal# " + name);

	string content;

	while( getline( input, line ) ) {
		if( line.find("input:") != string::npos ){
			inputs.push_back(line.substr(6));
		}
		if( line.find("output:") != string::npos ){
			outputs.push_back(line.substr(7));
		}
		if( line.find("content:") != string::npos ){
			content = line.substr(8);
			//for( vector<string>::iterator it = inputs.begin(); it != inputs.end(); it++ ){
				//myReplace(content, *it, name + "_" + *it);
			//}
			for( vector<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){
				myReplace(content, *it, name + "." + *it);
			}
			
		}
	}
	


	Model model = {content, name, inputs, outputs};
	models.push_back(model);

}

void dump_models(){

	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		fprintf(file, "(assert %s)\n", it->content.c_str());
	}
	fclose(file);
	

}

void dump_header(){
	FILE* file = fopen("/tmp/forest/model.smt2", "w");
	fprintf(file, "(set-option :produce-models true)\n");
	fprintf(file, "(set-logic AUFNIRA)\n");
	fclose(file);
}

void dump_inputs(){
	set<string> inputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> inputs = it->inputs;
		for( vector<string>::iterator it2 = inputs.begin(); it2 != inputs.end(); it2++ ){
			string input = *it2;
			inputs_set.insert(input);
		}
	}

	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	for( set<string>::iterator it = inputs_set.begin(); it != inputs_set.end(); it++ ){
		fprintf(file, "(declare-fun %s () Int)\n", it->c_str());
	}
	fclose(file);
	
	
}

void dump_outputs(){
	set<string> outputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> outputs = it->outputs;
		string name = it->name;
		for( vector<string>::iterator it2 = outputs.begin(); it2 != outputs.end(); it2++ ){
			string output = name + "." + *it2;
			outputs_set.insert(output);
		}
	}

	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	for( set<string>::iterator it = outputs_set.begin(); it != outputs_set.end(); it++ ){
		fprintf(file, "(declare-fun %s () Int)\n", it->c_str());
	}
	fclose(file);

}

void dump(){
	dump_header();
	dump_inputs();
	dump_outputs();
	dump_models();
}

void dump_get(){

	set<string> inputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> inputs = it->inputs;
		for( vector<string>::iterator it2 = inputs.begin(); it2 != inputs.end(); it2++ ){
			string input = *it2;
			inputs_set.insert(input);
		}
	}

	set<string> outputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> outputs = it->outputs;
		string name = it->name;
		for( vector<string>::iterator it2 = outputs.begin(); it2 != outputs.end(); it2++ ){
			string output = name + "." + *it2;
			outputs_set.insert(output);
		}
	}

	FILE* file = fopen("/tmp/forest/model.smt2", "a");

	for( set<string>::iterator it = inputs_set.begin(); it != inputs_set.end(); it++ ){
		fprintf(file, "(get-value (%s))\n", it->c_str());
	}

	for( set<string>::iterator it = outputs_set.begin(); it != outputs_set.end(); it++ ){
		fprintf(file, "(get-value (%s))\n", it->c_str());
	}

	fclose(file);

	
}

void dump_getsat(){
	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	fprintf(file, "(check-sat)\n");
	fclose(file);
}

void dump_exit(){
	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	fprintf(file, "(exit)\n");
	fclose(file);
}

void dump_check(string var1, string eq, string var2){
	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	fprintf(file, "(assert (not (%s %s %s)))\n", eq.c_str(), var1.c_str(), var2.c_str());
	fclose(file);
}

string check_sat(){

	char ret_s[128];

	stringstream command_ss;
	command_ss << "z3 /tmp/forest/model.smt2 > /tmp/forest/model_result";
	system(command_ss.str().c_str());

	FILE* file = fopen("/tmp/forest/model_result", "r");
	fscanf(file, "%s", ret_s);
	fclose(file);

	return string(ret_s);
	
}

void dump_assumptions(){
	FILE* file = fopen("/tmp/forest/model.smt2", "a");
	for( vector<string>::iterator it = assumptions.begin(); it != assumptions.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");
		string var1 = tokens[0];
		string eq = tokens[1];
		string var2 = tokens[2];
		fprintf(file, "(assert (%s %s %s))\n", eq.c_str(), var1.c_str(), var2.c_str());
	}
	fclose(file);
	
}

void get_counterexample(){

	assigns.clear();

	set<string> inputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> inputs = it->inputs;
		for( vector<string>::iterator it2 = inputs.begin(); it2 != inputs.end(); it2++ ){
			string input = *it2;
			inputs_set.insert(input);
		}
	}

	set<string> outputs_set;
	for( vector<Model>::iterator it = models.begin(); it != models.end(); it++ ){
		vector<string> outputs = it->outputs;
		string name = it->name;
		for( vector<string>::iterator it2 = outputs.begin(); it2 != outputs.end(); it2++ ){
			string output = name + "." + *it2;
			outputs_set.insert(output);
		}
	}



	for( set<string>::iterator it = inputs_set.begin(); it != inputs_set.end(); it++ ){
		Assign assign = {*it, "input", ""};
		assigns.push_back(assign);
	}

	for( set<string>::iterator it = outputs_set.begin(); it != outputs_set.end(); it++ ){
		Assign assign = {*it, "output", ""};
		assigns.push_back(assign);
	}
	
	ifstream input("/tmp/forest/model_result");
	string line;
	getline(input, line);

	int i = 0;
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, " ()");
		string value;
		string sign;
		if(tokens[1] == "-"){
			value = tokens[2];
			sign = "-";
		} else {
			value = tokens[1];
			sign = "";
		}
		value = sign + value;
		assigns[i].value = value;
		i++;
	}
	


}

void check(string command_str){

	vector<string> tokens = tokenize(command_str, " ");

	assert(tokens[0] == "check");

	string var1 = tokens[1];
	string eq   = tokens[2];
	string var2 = tokens[3];

	dump_header();
	dump_inputs();
	dump_outputs();
	dump_models();
	dump_assumptions();
	dump_check(var1, eq, var2);
	dump_getsat();
	dump_get();
	dump_exit();

	string res = check_sat();

	buffer_0.push_back( "#green#check#normal# " + var1 + " #red#" + eq + "#normal# " + var2 );

	if(res == "sat")
		buffer_0.push_back("   #red#FALSE#normal#");
	if(res == "unsat")
		buffer_0.push_back("   #green#TRUE#normal#");

	if(res == "sat"){
		get_counterexample();
	} else {
		assigns.clear();
	}

	
}

void assume(string command_str){

	vector<string> tokens = tokenize(command_str, " ");

	assert(tokens[0] == "assume");

	string var1 = tokens[1];
	string eq = tokens[2];
	string var2 = tokens[3];

	assumptions.push_back( var1 + " "  + eq + " " + var2);

	buffer_0.push_back( "#green#assume#normal# " + var1 + " #red#" + eq + "#normal# " + var2 );

}

void rm_assumptions(){
	assumptions.clear();
}

void do_command(){

	string command_s = string(command);
	vector<string> tokens = tokenize(command_s, " ");

	if(tokens[0] == "import"){
		import_model(command_s);
	} else if(tokens[0] == "dump"){
		dump();
	} else if(tokens[0] == "check"){
		check(command_s);
	} else if(tokens[0] == "assume"){
		assume(command_s);
	} else if(tokens[0] == "rm_assumptions"){
		rm_assumptions();
	} else {

	}
}

void back(){
	len_command--;
	command[len_command] = 0;
	mvwprintw(wins[3], 2, 6, "%s   ", command);
	move(LINES-3, 6+len_command);
}

int main(){

	initialize();

	initialize_wins();

	initialize_panels();

	begin_prompt();

	draw_win_0();
	draw_win_1();
	draw_win_2();
	draw_win_3();

	update();

	while(ch = getch()){
		switch(ch){
			case 27:
				finish();
				return 0;
			case 10:
				do_command();
				begin_prompt();
				break;
			case 127:
				back();
				break;
			case 9:
				complete_command();
				break;
			default:
				command_prompt(ch);
				break;

		}


		draw_win_0();
		draw_win_1();
		draw_win_2();
		draw_win_3();

		update();
	}
	return 0;
}


void win_show_box(WINDOW *win)
{	int startx, starty, height, width;

	getbegyx(win, starty, startx);
	getmaxyx(win, height, width);

	box(win, 0, 0);
}

void win_show_title(WINDOW *win, char *label) {

	int startx, starty, height, width;

	getbegyx(win, starty, startx);
	getmaxyx(win, height, width);

	box(win, 0, 0);
	mvwaddch(win, 2, 0, ACS_LTEE);
	mvwhline(win, 2, 1, ACS_HLINE, width - 2);
	mvwaddch(win, 2, width - 1, ACS_RTEE);
	
	print_in_middle(win, 1, 0, width, label, COLOR_PAIR(1));
}

void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string, chtype color) {
	int length, x, y;
	float temp;

	if(win == NULL)
		win = stdscr;
	getyx(win, y, x);
	if(startx != 0)
		x = startx;
	if(starty != 0)
		y = starty;
	if(width == 0)
		width = 80;

	length = strlen(string);
	temp = (width - length)/ 2;
	x = startx + (int)temp;
	wattron(win, color);
	mvwprintw(win, y, x, "%s", string);
	wattroff(win, color);
}

