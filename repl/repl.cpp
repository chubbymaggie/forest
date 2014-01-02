#include <panel.h>
#include <string.h>
#include <vector>
#include <string>
#include <assert.h>

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


WINDOW *wins[4];          // Windows
PANEL  *my_panels[4];     // Panels
PANEL  *top;              // Top panel
int ch;                   // Character type 
char command[128];        // repl command_prompt 
int len_command;          // command length
vector<string> buffer_0;  // buffer of windows 0
vector<string> buffer_1;  // buffer of windows 1
vector<string> buffer_2;  // buffer of windows 2
vector<Model>  models;    // Models

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
	wins[1] = newwin((LINES-5)/2  , COLS*1/4, 0          , COLS*3/4) ; win_show_title(wins[1], "Variables") ;
	wins[2] = newwin((LINES-5)/2+1, COLS*1/4, (LINES-5)/2, COLS*3/4) ; win_show_title(wins[2], "Counter Example") ;
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

	buffer_2.push_back("  Forest Read");
	buffer_2.push_back(" `-. .-------");
	buffer_2.push_back("    Y        ");
	buffer_2.push_back("    ,,  ,---,");
	buffer_2.push_back("   (_,\\/_\\_");
	buffer_2.push_back("     \\.\\_/_");
	buffer_2.push_back("     '-'   '-");
	buffer_2.push_back("             ");
	buffer_2.push_back("             ");
 
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

	if(buffer_2.size() < (LINES-5)/2-1 ){
		for ( unsigned int i = 0; i < buffer_2.size(); i++) {
			mvwprintw(wins[2], i+3, 1, "%s", buffer_2[i].c_str());
		}

	} else {

	}


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

	for ( unsigned int row = 1; row < 4; row++) {
		for ( unsigned int col = 1; col < COLS-1; col++) {
			mvwprintw(wins[3], row,col, " ");
		}
	}
	mvwprintw(wins[3], 2, 2, ">>> ");

	move(LINES-3, 6);
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

	vector<string> inputs; inputs.push_back("input1");
	vector<string> outputs; outputs.push_back("output1");

	Model model = {"", name, inputs, outputs};
	models.push_back(model);

	buffer_1.push_back("#magenta#" + name + "#normal#");
	buffer_1.push_back("#green# -" + inputs[0] + "#normal#");
	buffer_1.push_back("#red# -" + outputs[0] + "#normal#");

	buffer_0.push_back("#green#import#normal# " + tokens[1] + " #green#as#normal# " + name);

}

void do_command(){

	string command_s = string(command);
	vector<string> tokens = tokenize(command_s, " ");

	if(tokens[0] == "import"){
		import_model(command_s);
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
			default:
				command_prompt(ch);
				break;

		}

		draw_win_0();
		draw_win_1();
		draw_win_2();

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

