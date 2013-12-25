#include <panel.h>
#include <string.h>

void init_wins(WINDOW **wins, int n);
void win_show(WINDOW *win, char *label, int label_color);
void win_show_2(WINDOW *win, char *label, int label_color);
void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string, chtype color);

int main()
{	WINDOW *my_wins[4];
	PANEL  *my_panels[4];
	PANEL  *top;
	int ch;

	/* Initialize curses */
	initscr();
	start_color();
	cbreak();
	noecho();
	keypad(stdscr, TRUE);

	/* Initialize all the colors */
	init_pair(3, COLOR_BLUE, COLOR_BLACK);

	init_wins(my_wins, 4);
	
	/* Attach a panel to each window */
	my_panels[0] = new_panel(my_wins[0]);
	my_panels[1] = new_panel(my_wins[1]);
	my_panels[2] = new_panel(my_wins[2]);
	my_panels[3] = new_panel(my_wins[3]);

	/* Set up the user pointers to the next panel */
	set_panel_userptr(my_panels[0], my_panels[1]);
	set_panel_userptr(my_panels[1], my_panels[2]);
	set_panel_userptr(my_panels[2], my_panels[3]);
	set_panel_userptr(my_panels[3], my_panels[0]);

	/* Update the stacking order. 2nd panel will be on top */
	update_panels();

	/* Show it on the screen */
	doupdate();

	top = my_panels[2];
	while((ch = getch()) != 27)
	{	switch(ch)
		{	case 9:
				top = (PANEL *)panel_userptr(top);
				top_panel(top);
				break;
		}
		update_panels();
		doupdate();
	}
	endwin();
	return 0;
}

/* Put all the windows */
void init_wins(WINDOW **wins, int n)
{	int x, y, i;
	char label[80];

	wins[0] = newwin(LINES-5       , COLS*3/4 , 0           , 0)        ; sprintf(label , "Main Window") ; win_show_2(wins[0] , label , 3) ;
	wins[1] = newwin((LINES-5)/2   , COLS*1/4 , 0           , COLS*3/4) ; sprintf(label , "Variables")   ; win_show(wins[1]   , label , 3) ;
	wins[2] = newwin((LINES-5)/2+1 , COLS*1/4 , (LINES-5)/2 , COLS*3/4) ; sprintf(label , "Solution")    ; win_show(wins[2]   , label , 3) ;
	wins[3] = newwin(5             , COLS     , LINES-5     , 0)        ; sprintf(label , "REPL")        ; win_show_2(wins[3] , label , 3) ;

}

/* Show the window with a border and a label */
void win_show_2(WINDOW *win, char *label, int label_color)
{	int startx, starty, height, width;

	getbegyx(win, starty, startx);
	getmaxyx(win, height, width);

	box(win, 0, 0);
}

/* Show the window with a border and a label */
void win_show(WINDOW *win, char *label, int label_color)
{	int startx, starty, height, width;

	getbegyx(win, starty, startx);
	getmaxyx(win, height, width);

	box(win, 0, 0);
	mvwaddch(win, 2, 0, ACS_LTEE);
	mvwhline(win, 2, 1, ACS_HLINE, width - 2);
	mvwaddch(win, 2, width - 1, ACS_RTEE);
	
	print_in_middle(win, 1, 0, width, label, COLOR_PAIR(label_color));
}

void print_in_middle(WINDOW *win, int starty, int startx, int width, char *string, chtype color)
{	int length, x, y;
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
	refresh();
}
