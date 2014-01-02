#include <panel.h>
#include <string.h>

void init_wins(WINDOW **wins, int n);
void win_show_title(WINDOW *win, char *label);
void win_show_box(WINDOW *win);
void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string, chtype color);


WINDOW *wins[4];       // Windows
PANEL  *my_panels[4];  // Panels
PANEL  *top;           // Top panel
int ch;                // Character type 
char command[128];     // repl command_prompt 
int len_command;       // command length

void initialize(){
	/* Initialize curses */
	initscr();
	start_color();

	/* Initialize all the colors */
	init_pair(1, COLOR_BLUE, COLOR_BLACK);
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

	scrollok(wins[0], TRUE);

	int n = 0;

	mvwprintw(wins[0], n+2,2, "  Forest Read-Eval-Print-Loop ");
	mvwprintw(wins[0], n+3,2, " `-. .------------------------");
	mvwprintw(wins[0], n+4,2, "    Y                         ");
	mvwprintw(wins[0], n+5,2, "    ,,  ,---,                 ");
	mvwprintw(wins[0], n+6,2, "   (_,\\/_\\_/_\\                ");
	mvwprintw(wins[0], n+7,2, "     \\.\\_/_\\_/>               ");
	mvwprintw(wins[0], n+8,2, "     '-'   '-'                ");

 
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

	char prompt[128] = ">>> ";
	for ( unsigned int i = 0; i < LINES; i++) {
		strcat(prompt, " ");
	}

	mvwprintw(wins[3], 2, 2, "%s", prompt);

	move(LINES-3, 6);
	strcpy(command, "");
	len_command = 0;
}

void finish(){
	endwin();
}

void do_command(){
	mvwprintw(wins[0], 2, 2, "%s", command);
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

