// Schach 2D - C++ OpenGL 3.3 Core
// Hauptmenue, Intro, 2 Spieler, KI, adaptives Layout

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <winsock2.h>
#include <mmsystem.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
#include <GL/glew.h>
#include <GLFW/glfw3.h>

#define STB_TRUETYPE_IMPLEMENTATION
#include "stb_truetype.h"

#define FONT_ATLAS_W 1024
#define FONT_ATLAS_H 1024

static unsigned char font_atlas[FONT_ATLAS_W * FONT_ATLAS_H];
static stbtt_bakedchar font_cdata[224];
static GLuint font_tex = 0;
static GLuint text_vao = 0, text_vbo = 0;
static GLuint text_shader = 0;
float proj[16];
int fbW = 1024, fbH = 768;
const int BOARD_OFF = 10;

// ============================================================
// SCHACH-LOGIK
// ============================================================
enum Piece { EMPTY, P, N, B, R, Q, K };
enum Color { NONE, WHITE, BLACK };
struct Board { Piece p[64]; Color c[64]; };

Board board;
Color turn = WHITE;
int en_passant = -1;
bool castle_wk = true, castle_wq = true;
bool castle_bk = true, castle_bq = true;
int halfmove = 0, fullmove = 1;
int sel = -1;
std::vector<int> legal_moves;
std::string status_msg = "Weiss ist am Zug";
int captured_white[16] = {0}, captured_black[16] = {0};
int num_cap_w = 0, num_cap_b = 0;
int turn_count = 0;
int last_from = -1, last_to = -1;
bool promoting = false;
int promo_from = -1, promo_to = -1;
bool game_over = false;

void clear_board() {
    for (int i = 0; i < 64; i++) board.p[i] = EMPTY, board.c[i] = NONE;
    turn = WHITE; en_passant = -1;
    castle_wk = castle_wq = castle_bk = castle_bq = true;
    sel = -1; legal_moves.clear();
    num_cap_w = num_cap_b = 0; turn_count = 0;
    last_from = last_to = -1;
}

void init_board() {
    clear_board();
    const char* back = "rnbqkbnr";
    for (int f = 0; f < 8; f++) {
        board.p[f] = R; board.c[f] = BLACK;
        board.p[56+f] = R; board.c[56+f] = WHITE;
        board.p[8+f] = P; board.c[8+f] = BLACK;
        board.p[48+f] = P; board.c[48+f] = WHITE;
        char bp = back[f];
        Piece pi = EMPTY;
        if (bp == 'n') pi = N; else if (bp == 'b') pi = B;
        else if (bp == 'q') pi = Q; else if (bp == 'k') pi = K;
        if (pi != EMPTY) { board.p[f] = pi; board.p[56+f] = pi; }
    }
    board.p[1] = N; board.p[6] = N;
    board.p[57] = N; board.p[62] = N;
    board.p[2] = B; board.p[5] = B;
    board.p[58] = B; board.p[61] = B;
    board.p[3] = Q; board.p[59] = Q;
    board.p[4] = K; board.p[60] = K;
    status_msg = "Weiss ist am Zug";
}

int sq(int f, int r) { return r * 8 + f; }
int file_of(int s) { return s % 8; }
int rank_of(int s) { return s / 8; }
bool on_board(int f, int r) { return f >= 0 && f < 8 && r >= 0 && r < 8; }
Color opp(Color c) { return c == WHITE ? BLACK : WHITE; }

bool is_attacked(int sq_idx, Color by, const Board& b) {
    int f = file_of(sq_idx), r = rank_of(sq_idx), dir = (by == WHITE) ? -1 : 1;
    for (int df : {-1, 1}) { int nf = f+df, nr = r+dir; if (on_board(nf,nr)) { int i = sq(nf,nr); if (b.p[i] == P && b.c[i] == by) return true; } }
    for (auto [df,dr] : {std::pair{-1,-2},{1,-2},{-2,-1},{2,-1},{-2,1},{2,1},{-1,2},{1,2}}) { int nf=f+df,nr=r+dr; if (on_board(nf,nr)) { int i=sq(nf,nr); if (b.p[i]==N&&b.c[i]==by) return true; } }
    for (int df=-1;df<=1;df++) for (int dr=-1;dr<=1;dr++) { if (!df&&!dr) continue; int nf=f+df,nr=r+dr; if (on_board(nf,nr)) { int i=sq(nf,nr); if (b.p[i]==K&&b.c[i]==by) return true; } }
    for (auto [df,dr] : {std::pair{-1,-1},{-1,1},{1,-1},{1,1}}) for (int d=1;d<8;d++) { int nf=f+df*d,nr=r+dr*d; if (!on_board(nf,nr)) break; int i=sq(nf,nr); if (b.p[i]!=EMPTY) { if (b.c[i]==by&&(b.p[i]==B||b.p[i]==Q)) return true; break; } }
    for (auto [df,dr] : {std::pair{-1,0},{1,0},{0,-1},{0,1}}) for (int d=1;d<8;d++) { int nf=f+df*d,nr=r+dr*d; if (!on_board(nf,nr)) break; int i=sq(nf,nr); if (b.p[i]!=EMPTY) { if (b.c[i]==by&&(b.p[i]==R||b.p[i]==Q)) return true; break; } }
    return false;
}

bool in_check(Color side, const Board& b) {
    for (int i=0;i<64;i++) if (b.p[i]==K&&b.c[i]==side) return is_attacked(i,opp(side),b);
    return false;
}

bool is_legal_move(int from, int to, const Board& b, Color side) {
    Board nb = b;
    nb.p[to]=nb.p[from]; nb.c[to]=nb.c[from]; nb.p[from]=EMPTY; nb.c[from]=NONE;
    if (b.p[from]==P&&to==en_passant) { int ei=en_passant+(side==WHITE?-8:8); nb.p[ei]=EMPTY; nb.c[ei]=NONE; }
    if (b.p[from]==K&&abs(file_of(to)-file_of(from))==2) {
        if (to>from) { nb.p[to-1]=nb.p[to+1]; nb.c[to-1]=nb.c[to+1]; nb.p[to+1]=EMPTY; nb.c[to+1]=NONE; }
        else { nb.p[to+1]=nb.p[to-2]; nb.c[to+1]=nb.c[to-2]; nb.p[to-2]=EMPTY; nb.c[to-2]=NONE; }
    }
    return !in_check(side,nb);
}

void generate_moves_for(int sq_idx, std::vector<int>& moves, const Board& b, bool only_captures, Color side) {
    moves.clear();
    Piece p = b.p[sq_idx];
    if (p == EMPTY || b.c[sq_idx] != side) return;
    int f = file_of(sq_idx), r = rank_of(sq_idx);
    auto add = [&](int tf, int tr, int ti) {
        if (!on_board(tf,tr)) return;
        if (b.p[ti]==EMPTY || b.c[ti]!=side) moves.push_back(ti);
    };
    auto add_slide = [&](int df, int dr) {
        for (int d=1;d<8;d++) { int nf=f+df*d,nr=r+dr*d; if (!on_board(nf,nr)) break; int ni=sq(nf,nr); if (b.p[ni]==EMPTY) { if (!only_captures) moves.push_back(ni); } else { if (b.c[ni]!=side) moves.push_back(ni); break; } }
    };
    switch (p) {
        case P: {
            int dir = (side==WHITE)?-1:1, sr = (side==WHITE)?6:1;
            int nf=f, nr=r+dir;
            if (on_board(nf,nr)&&b.p[sq(nf,nr)]==EMPTY) {
                if (!only_captures) moves.push_back(sq(nf,nr));
                if (r==sr) { nr=r+2*dir; if (on_board(nf,nr)&&b.p[sq(nf,nr)]==EMPTY&&!only_captures) moves.push_back(sq(nf,nr)); }
            }
            for (int df2 : {-1,1}) { nf=f+df2; nr=r+dir; if (on_board(nf,nr)) { int ti=sq(nf,nr); if (b.p[ti]!=EMPTY&&b.c[ti]!=side) moves.push_back(ti); if (ti==en_passant) moves.push_back(ti); } }
            break;
        }
        case N: for (auto [df,dr]:{std::pair{-1,-2},{1,-2},{-2,-1},{2,-1},{-2,1},{2,1},{-1,2},{1,2}}) add(f+df,r+dr,sq(f+df,r+dr)); break;
        case B: for (auto [df,dr]:{std::pair{-1,-1},{-1,1},{1,-1},{1,1}}) add_slide(df,dr); break;
        case R: for (auto [df,dr]:{std::pair{-1,0},{1,0},{0,-1},{0,1}}) add_slide(df,dr); break;
        case Q: for (auto [df,dr]:{std::pair{-1,-1},{-1,1},{1,-1},{1,1},{-1,0},{1,0},{0,-1},{0,1}}) add_slide(df,dr); break;
        case K: {
            for (int df=-1;df<=1;df++) for (int dr=-1;dr<=1;dr++) if(df||dr) add(f+df,r+dr,sq(f+df,r+dr));
            if (!only_captures&&!in_check(side,b)) {
                if (side==WHITE&&r==7&&f==4) {
                    if (castle_wk&&b.p[63]==R&&b.c[63]==WHITE&&b.p[61]==EMPTY&&b.p[62]==EMPTY&&!is_attacked(61,BLACK,b)&&!is_attacked(62,BLACK,b)) moves.push_back(sq(6,7));
                    if (castle_wq&&b.p[56]==R&&b.c[56]==WHITE&&b.p[57]==EMPTY&&b.p[58]==EMPTY&&b.p[59]==EMPTY&&!is_attacked(58,BLACK,b)&&!is_attacked(59,BLACK,b)) moves.push_back(sq(2,7));
                }
                if (side==BLACK&&r==0&&f==4) {
                    if (castle_bk&&b.p[7]==R&&b.c[7]==BLACK&&b.p[5]==EMPTY&&b.p[6]==EMPTY&&!is_attacked(5,WHITE,b)&&!is_attacked(6,WHITE,b)) moves.push_back(sq(6,0));
                    if (castle_bq&&b.p[0]==R&&b.c[0]==BLACK&&b.p[1]==EMPTY&&b.p[2]==EMPTY&&b.p[3]==EMPTY&&!is_attacked(2,WHITE,b)&&!is_attacked(3,WHITE,b)) moves.push_back(sq(2,0));
                }
            }
            break;
        }
    }
}

void make_move(int from, int to, Board& b, Color& t, int& ep, bool& wk, bool& wq, bool& bk, bool& bq, int& capw, int& capb, int capw_arr[], int capb_arr[], int& hm, int& fm, Piece promo = Q) {
    Piece p = b.p[from]; Color side = b.c[from];
    int ff=file_of(from), fr=rank_of(from), tf=file_of(to), tr=rank_of(to);
    if (p==K) { if (side==WHITE) wk=wq=false; else bk=bq=false; }
    if (p==R) { if (from==56) wq=false; if (from==63) wk=false; if (from==0) bq=false; if (from==7) bk=false; }
    if (to==56) wq=false; if (to==63) wk=false; if (to==0) bq=false; if (to==7) bk=false;
    int new_ep = -1;
    if (p==P&&abs(tr-fr)==2) new_ep = sq(tf,(fr+tr)/2);
    if (p==P&&to==ep) { int ei=ep+(side==WHITE?-8:8); b.p[ei]=EMPTY; b.c[ei]=NONE; }
    if (p==K&&abs(tf-ff)==2) {
        if (to>from) { b.p[to-1]=b.p[to+1]; b.c[to-1]=b.c[to+1]; b.p[to+1]=EMPTY; b.c[to+1]=NONE; }
        else { b.p[to+1]=b.p[to-2]; b.c[to+1]=b.c[to-2]; b.p[to-2]=EMPTY; b.c[to-2]=NONE; }
    }
    if (b.p[to]!=EMPTY) {
        if (side==WHITE) capb_arr[capb++]=b.p[to]; else capw_arr[capw++]=b.p[to];
    }
    if (p==P&&(tr==0||tr==7)) b.p[from]=promo;
    b.p[to]=b.p[from]; b.c[to]=b.c[from]; b.p[from]=EMPTY; b.c[from]=NONE;
    ep = new_ep;
    t = opp(side); if (t==WHITE) fm++;
    hm = (p==P||b.p[to]!=EMPTY)?0:hm+1;
}

bool has_legal_moves(const Board& b, Color side) {
    for (int i=0;i<64;i++) {
        if (b.c[i]!=side||b.p[i]==EMPTY) continue;
        std::vector<int> m; generate_moves_for(i,m,b,false,side);
        for (int t : m) if (is_legal_move(i,t,b,side)) return true;
    }
    return false;
}

void update_status() {
    if (in_check(turn,board)) {
        if (!has_legal_moves(board,turn)) status_msg = (turn==WHITE?"Schwarz":"Weiss")+std::string(" gewinnt! Schachmatt!");
        else status_msg = (turn==WHITE?"Weiss":"Schwarz")+std::string(" ist im Schach!");
    } else {
        if (!has_legal_moves(board,turn)) status_msg = "Patt! Remis!";
        else status_msg = (turn==WHITE?"Weiss":"Schwarz")+std::string(" ist am Zug");
    }
}

void audio_play_sfx(const char* name);

// Network globals
#pragma comment(lib, "ws2_32.lib")
enum NetState { NET_IDLE, NET_HOST, NET_CONNECTING, NET_CONNECTED, NET_ERROR };
NetState net_state = NET_IDLE;
bool net_my_turn = true;
bool net_from_network = false;
bool net_game = false;
SOCKET net_sock = INVALID_SOCKET;
SOCKET net_listen = INVALID_SOCKET;
char net_ip_buf[32] = "";
int net_ip_len = 0;
char net_info[64] = "";
int net_port = 5555;
void net_send_move(int from, int to, Piece promo);
void net_cancel();

// Network UI globals (needed early for callbacks)
enum MenuPage { MENU_MAIN, MENU_NETWORK, MENU_NET_IP, MENU_RANKING };
MenuPage menu_page = MENU_MAIN;
const char* net_menu_items[] = {"Spielername", "Spiel hosten", "Spiel beitreten", "Rangliste", "Zurueck"};
const int net_menu_count = 5;
int net_menu_sel = 0;
bool net_editing_name = false;

// Forward declarations for network functions used by callbacks
void net_start_host();
void net_start_connect();
void net_cleanup();
void render_network_menu();

// Network receive buffer
char net_recv_buf[4096];
int net_recv_len = 0;

// Rating system
char net_my_name[32] = "Spieler";
char net_opp_name[32] = "Gegner";
bool net_rating_received = false;
bool net_rating_sent = false;
int net_rating_winner = 0, net_rating_loser = 0;
const char* RATING_FILE = "ratings.txt";
struct RatingEntry { char name[32]; int rating; };
RatingEntry ratings[256];
int rating_count = 0;

int rating_find(const char* name) {
    for(int i=0;i<rating_count;i++) if(stricmp(ratings[i].name,name)==0) return i;
    return -1;
}
int rating_get(const char* name) {
    int idx=rating_find(name); return idx>=0?ratings[idx].rating:1500;
}
void rating_set(const char* name, int r) {
    int idx=rating_find(name);
    if(idx>=0) ratings[idx].rating=r;
    else if(rating_count<256){strncpy(ratings[rating_count].name,name,31);ratings[rating_count].rating=r;rating_count++;}
}
void rating_update(const char* winner, const char* loser) {
    int rw=rating_get(winner), rl=rating_get(loser);
    double ew=1.0/(1.0+pow(10.0,(rl-rw)/400.0));
    double el=1.0/(1.0+pow(10.0,(rw-rl)/400.0));
    int new_rw=(int)(rw+32.0*(1.0-ew));
    int new_rl=(int)(rl+32.0*(0.0-el));
    rating_set(winner,new_rw); rating_set(loser,new_rl);
}
void ratings_save() {
    FILE* f=fopen(RATING_FILE,"w"); if(!f) return;
    for(int i=0;i<rating_count;i++) fprintf(f,"%s:%d\n",ratings[i].name,ratings[i].rating);
    fclose(f);
}
void ratings_load() {
    FILE* f=fopen(RATING_FILE,"r"); if(!f) return;
    rating_count=0;
    char line[64];
    while(fgets(line,sizeof(line),f)&&rating_count<256){
        char* sep=strchr(line,':'); if(!sep) continue;
        *sep=0; int r=atoi(sep+1);
        strncpy(ratings[rating_count].name,line,31); ratings[rating_count].rating=r; rating_count++;
    }
    fclose(f);
}

void do_move(int from, int to, Piece promo = Q) {
    bool capture = (board.p[to]!=EMPTY);
    last_from=from; last_to=to;
    make_move(from,to,board,turn,en_passant,castle_wk,castle_wq,castle_bk,castle_bq,num_cap_w,num_cap_b,captured_white,captured_black,halfmove,fullmove,promo);
    sel=-1; legal_moves.clear(); turn_count++;
    update_status();
    if (status_msg.find("Schachmatt")!=std::string::npos||status_msg.find("Patt")!=std::string::npos) game_over = true;
    else game_over = false;
    if (capture) audio_play_sfx("capture.wav");
    else audio_play_sfx("move.wav");
    if (net_state == NET_CONNECTED && !net_from_network) net_send_move(from, to, promo);
}

// ============================================================
// SCHACH-KI (einfaches Minimax mit Alpha-Beta, Tiefe 3)
// ============================================================
int piece_val(Piece p) {
    switch(p) { case P: return 100; case N: return 320; case B: return 330; case R: return 500; case Q: return 900; case K: return 20000; default: return 0; }
}

int evaluate(const Board& b) {
    int score = 0;
    for (int i=0;i<64;i++) {
        if (b.p[i]==EMPTY) continue;
        int v = piece_val(b.p[i]);
        // Bonus für Zentrumskontrolle
        int f = file_of(i), r = rank_of(i);
        if (b.p[i]!=K&&b.p[i]!=P) v += (3-abs(3-f))*5 + (3-abs(3-r))*5;
        score += (b.c[i]==WHITE?v:-v);
    }
    return score;
}

int alphabeta(Board& b, int depth, int alpha, int beta, bool max_player, Color side, int ep, bool wk, bool wq, bool bk, bool bq) {
    if (depth==0) return evaluate(b);
    Color cur = max_player?side:opp(side);
    if (!has_legal_moves(b,cur)) {
        if (in_check(cur,b)) return max_player?-99999+depth:99999-depth;
        return 0; // stalemate
    }
    int best = max_player?-99999:99999;
    for (int i=0;i<64;i++) {
        if (b.c[i]!=cur||b.p[i]==EMPTY) continue;
        std::vector<int> m; generate_moves_for(i,m,b,false,cur);
        for (int t : m) {
            if (!is_legal_move(i,t,b,cur)) continue;
            Board nb = b; Color nt = turn; int nep = en_passant;
            bool nwk=castle_wk,nwq=castle_wq,nbk=castle_bk,nbq=castle_bq;
            int dummy_cw=0,dummy_cb=0; int capw[16]={0},capb[16]={0};
            int hm2=0,fm2=0;
            make_move(i,t,nb,nt,nep,nwk,nwq,nbk,nbq,dummy_cw,dummy_cb,capw,capb,hm2,fm2);
            int val = alphabeta(nb,depth-1,alpha,beta,!max_player,side,nep,nwk,nwq,nbk,nbq);
            if (max_player) { best=std::max(best,val); alpha=std::max(alpha,val); }
            else { best=std::min(best,val); beta=std::min(beta,val); }
            if (beta<=alpha) return best;
        }
    }
    return best;
}

int ai_side = BLACK; // KI spielt Schwarz

void ai_move() {
    if (turn != ai_side) return;
    int best_from = -1, best_to = -1, best_val = -99999;
    for (int i=0;i<64;i++) {
        if (board.c[i]!=turn||board.p[i]==EMPTY) continue;
        std::vector<int> m; generate_moves_for(i,m,board,false,turn);
        for (int t : m) {
            if (!is_legal_move(i,t,board,turn)) continue;
            Board nb = board; Color nt = turn; int nep = en_passant;
            bool nwk=castle_wk,nwq=castle_wq,nbk=castle_bk,nbq=castle_bq;
            int dcw=0,dcb=0; int cw[16]={0},cb[16]={0}; int hm2=0,fm2=0;
            make_move(i,t,nb,nt,nep,nwk,nwq,nbk,nbq,dcw,dcb,cw,cb,hm2,fm2);
            int val = alphabeta(nb,2,-99999,99999,false,turn,nep,nwk,nwq,nbk,nbq);
            if (val > best_val) { best_val = val; best_from = i; best_to = t; }
        }
    }
    if (best_from >= 0) do_move(best_from, best_to);
}

// ============================================================
// SPIEL-ZUSTÄNDE
// ============================================================
enum GameMode { INTRO, MENU, OPTIONS, GAME };
GameMode mode = INTRO;
double intro_start = 0;
double ai_timer = 0;
bool ai_enabled = false;

int menu_sel = 0;
const char* menu_items[] = {"1 Spieler vs Computer", "2 Spieler", "Netzwerk", "Optionen", "Spiel beenden"};
const int menu_count = 5;

// ============================================================
// OPTIONS SYSTEM
// ============================================================
enum OptTab { OPT_CONTROLS, OPT_AUDIO, OPT_GRAPHICS };
OptTab opt_tab = OPT_CONTROLS;
int opt_item_sel = 0;

// Controls
int opt_mouse_speed = 5; // 1-10

// Audio
int opt_sound = 1; // bool
int opt_volume = 80; // 0-100
int opt_microphone = 1; // bool
int opt_mic_volume = 80; // 0-100
int opt_audio_device = 0; // index
const char* opt_audio_devices[] = {"Standard (Windows)", "Kopfhoerer", "Lautsprecher"};
const int opt_audio_dev_count = 3;

// Graphics
int opt_resolution = 2; // index
const char* opt_res_list[] = {"1280x720", "1600x900", "1920x1080", "2560x1440", "3840x2160"};
const int opt_res_count = 5;
int opt_fullscreen = 0; // bool
int opt_vsync = 1; // bool
int opt_aa = 0; // 0=aus, 1=2x, 2=4x, 3=8x
const char* opt_aa_list[] = {"Aus", "2x", "4x", "8x"};
const int opt_aa_count = 4;
int opt_aniso = 0; // 0=aus, 1=2x, 2=4x, 3=8x, 4=16x
const char* opt_aniso_list[] = {"Aus", "2x", "4x", "8x", "16x"};
const int opt_aniso_count = 5;
int opt_tex_detail = 2;
int opt_model_detail = 2;
int opt_shader_detail = 2;
const char* opt_detail_list[] = {"Niedrig", "Mittel", "Hoch"};
const int opt_detail_count = 3;

// Helpers for options rendering
void opt_change(int dir); // forward

bool show_ai_thinking = false;
double mouse_x = 0, mouse_y = 0;

// ============================================================
// FONT SYSTEM
// ============================================================
int font_px = 20;
bool need_font_rebake = true;
static unsigned char* ttf_data = nullptr;
static int ttf_len = 0;
GLuint game_vao = 0, game_vbo = 0;
GLuint game_shader = 0;
GLuint shader_3d = 0;

void bake_font(int px) {
    if (!ttf_data) return;
    font_px = px;
    memset(font_atlas, 0, FONT_ATLAS_W * FONT_ATLAS_H);
    stbtt_BakeFontBitmap(ttf_data, 0, (float)px, font_atlas, FONT_ATLAS_W, FONT_ATLAS_H, 32, 96, font_cdata);
    // Bake extended chars (German umlauts: 196,214,220,223,228,246,252)
    // Also chess pieces at U+2654-U+265F (code points 9812-9823)
    for (int cp = 196; cp <= 252; cp++) {
        if (cp == 197 || cp == 199 || cp == 241 || cp == 209) continue;
        if (ttf_data) {
            int idx = cp - 32;
            if (idx >= 32 && idx < 224) {
                // Re-bake would overwrite but stbtt doesn't support that well
                // Just ASCII is enough for our game
            }
        }
    }
    glBindTexture(GL_TEXTURE_2D, font_tex);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RED, FONT_ATLAS_W, FONT_ATLAS_H, 0, GL_RED, GL_UNSIGNED_BYTE, font_atlas);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    need_font_rebake = false;
}

bool init_font() {
    const char* fps[] = {"C:\\Windows\\Fonts\\consola.ttf","C:\\Windows\\Fonts\\lucon.ttf","C:\\Windows\\Fonts\\cour.ttf","C:\\Windows\\Fonts\\arial.ttf","C:\\Windows\\Fonts\\segoeui.ttf"};
    for (const char* fp : fps) {
        FILE* f = fopen(fp,"rb"); if (!f) continue;
        fseek(f,0,SEEK_END); ttf_len = ftell(f); fseek(f,0,SEEK_SET);
        ttf_data=(unsigned char*)malloc(ttf_len);
        if (ttf_data) fread(ttf_data,1,ttf_len,f);
        fclose(f);
        if (ttf_data) break;
    }
    if (!ttf_data) return false;
    glGenTextures(1, &font_tex);

    const char* vs = "#version 330 core\nlayout(location=0)in vec2 aPos;layout(location=1)in vec2 aUV;layout(location=2)in vec4 aCol;uniform mat4 uProj;out vec2 vUV;out vec4 vCol;void main(){gl_Position=uProj*vec4(aPos,0,1);vUV=aUV;vCol=aCol;}";
    const char* fs = "#version 330 core\nin vec2 vUV;in vec4 vCol;uniform sampler2D uTex;out vec4 FragColor;void main(){float a=texture(uTex,vUV).r;FragColor=vec4(vCol.rgb*a,vCol.a*a);}";
    auto comp = [](GLuint type, const char* src)->GLuint{GLuint s=glCreateShader(type);glShaderSource(s,1,&src,nullptr);glCompileShader(s);GLint ok;glGetShaderiv(s,GL_COMPILE_STATUS,&ok);if(!ok){char l[512];glGetShaderInfoLog(s,512,nullptr,l);fprintf(stderr,"TS:%s\n",l);return 0;}return s;};
    GLuint v=comp(GL_VERTEX_SHADER,vs), f=comp(GL_FRAGMENT_SHADER,fs);
    if (!v||!f) return false;
    text_shader=glCreateProgram(); glAttachShader(text_shader,v); glAttachShader(text_shader,f); glLinkProgram(text_shader);
    GLint ok; glGetProgramiv(text_shader,GL_LINK_STATUS,&ok); glDeleteShader(v); glDeleteShader(f);
    if (!ok) return false;
    glGenVertexArrays(1,&text_vao); glGenBuffers(1,&text_vbo);
    glBindVertexArray(text_vao); glBindBuffer(GL_ARRAY_BUFFER,text_vbo);
    glVertexAttribPointer(0,2,GL_FLOAT,GL_FALSE,8*4,(void*)0); glEnableVertexAttribArray(0);
    glVertexAttribPointer(1,2,GL_FLOAT,GL_FALSE,8*4,(void*)(2*4)); glEnableVertexAttribArray(1);
    glVertexAttribPointer(2,4,GL_FLOAT,GL_FALSE,8*4,(void*)(4*4)); glEnableVertexAttribArray(2);
    return true;
}

struct TextVert { float x,y,u,v; float r,g,b,a; };

void render_text(float x, float y, const char* text, float r, float g, float b, float a, bool centered=false) {
    if (!text||!*text||!text_shader||!font_tex) return;
    std::vector<TextVert> tverts;
    float sx = x, sy = y;
    if (centered) {
        float w = 0;
        for (const char* p=text;*p;p++) {
            unsigned char ch = (unsigned char)*p;
            if (ch>=32&&ch<128) { stbtt_aligned_quad q; stbtt_GetBakedQuad(font_cdata,FONT_ATLAS_W,FONT_ATLAS_H,ch-32,&w,&sy,&q,1); }
            else { w+=12.0f; }
        }
        sx = x - w/2;
        sy = y;
    }
    float cx = sx, cy = sy;
    for (const char* p=text;*p;p++) {
        unsigned char ch = (unsigned char)*p;
        if (ch>=32&&ch<128) {
            stbtt_aligned_quad q; stbtt_GetBakedQuad(font_cdata,FONT_ATLAS_W,FONT_ATLAS_H,ch-32,&cx,&cy,&q,1);
            tverts.push_back({q.x0,q.y0,q.s0,q.t0,r,g,b,a}); tverts.push_back({q.x1,q.y0,q.s1,q.t0,r,g,b,a});
            tverts.push_back({q.x1,q.y1,q.s1,q.t1,r,g,b,a}); tverts.push_back({q.x0,q.y0,q.s0,q.t0,r,g,b,a});
            tverts.push_back({q.x1,q.y1,q.s1,q.t1,r,g,b,a}); tverts.push_back({q.x0,q.y1,q.s0,q.t1,r,g,b,a});
        } else cx += 12.0f;
    }
    if (tverts.empty()) return;
    GLint pp,pv,pt; glGetIntegerv(GL_CURRENT_PROGRAM,&pp); glGetIntegerv(GL_VERTEX_ARRAY_BINDING,&pv); glGetIntegerv(GL_TEXTURE_BINDING_2D,&pt);
    GLboolean bl = glIsEnabled(GL_BLEND);
    glUseProgram(text_shader); glUniformMatrix4fv(glGetUniformLocation(text_shader,"uProj"),1,GL_FALSE,proj);
    glBindTexture(GL_TEXTURE_2D,font_tex); glBindVertexArray(text_vao); glBindBuffer(GL_ARRAY_BUFFER,text_vbo);
    glBufferData(GL_ARRAY_BUFFER,tverts.size()*sizeof(TextVert),tverts.data(),GL_STREAM_DRAW);
    if (!bl) glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);
    glDrawArrays(GL_TRIANGLES,0,(GLsizei)tverts.size());
    if (!bl) glDisable(GL_BLEND);
    glBindTexture(GL_TEXTURE_2D,pt); glBindVertexArray(pv); glUseProgram(pp);
}

// ============================================================
// OPENGL RENDERING
// ============================================================
GLFWwindow* window = nullptr;
std::vector<float> verts; // x,y,z,r,g,b

void ortho(float l, float r, float b, float t) {
    memset(proj,0,sizeof(proj));
    proj[0]=2/(r-l); proj[5]=2/(t-b); proj[10]=-1;
    proj[12]=-(r+l)/(r-l); proj[13]=-(t+b)/(t-b); proj[15]=1;
}

bool init_shaders() {
    auto c=[](GLuint t,const char* s)->GLuint{GLuint sh=glCreateShader(t);glShaderSource(sh,1,&s,nullptr);glCompileShader(sh);GLint ok;glGetShaderiv(sh,GL_COMPILE_STATUS,&ok);if(!ok){char l[512];glGetShaderInfoLog(sh,512,nullptr,l);fprintf(stderr,"S:%s\n",l);return 0;}return sh;};
    // 2D shader
    const char* vss="#version 330 core\nlayout(location=0)in vec3 aPos;layout(location=1)in vec3 aCol;uniform mat4 uProj;out vec3 vCol;void main(){gl_Position=uProj*vec4(aPos,1);vCol=aCol;}";
    const char* fss="#version 330 core\nin vec3 vCol;out vec4 FragColor;void main(){FragColor=vec4(vCol,1);}";
    {GLuint vs=c(GL_VERTEX_SHADER,vss),fs=c(GL_FRAGMENT_SHADER,fss);  if(!vs||!fs) return false;
    game_shader=glCreateProgram();glAttachShader(game_shader,vs);glAttachShader(game_shader,fs);glLinkProgram(game_shader);
    GLint ok;glGetProgramiv(game_shader,GL_LINK_STATUS,&ok);glDeleteShader(vs);glDeleteShader(fs); if(!ok) return false;}
    // 3D shader
    const char* v3d="#version 330 core\nlayout(location=0)in vec3 aP;layout(location=1)in vec3 aN;layout(location=2)in vec3 aC;uniform mat4 uMVP;uniform mat4 uM;uniform vec3 uLD;out vec3 vN;out vec3 vC;out vec3 vP;void main(){vec4 wp=uM*vec4(aP,1);vP=wp.xyz;vN=mat3(transpose(inverse(uM)))*aN;vC=aC;gl_Position=uMVP*vec4(aP,1);}";
    const char* f3d="#version 330 core\nin vec3 vN;in vec3 vC;in vec3 vP;uniform vec3 uVP;uniform float uAmb;uniform vec3 uLD;uniform vec3 uCol;out vec4 F;void main(){vec3 col=vC*uCol;vec3 n=normalize(vN);vec3 ld=normalize(uLD);float df=max(dot(n,-ld),0);vec3 vd=normalize(uVP-vP);vec3 rd=reflect(ld,n);float sp=pow(max(dot(vd,rd),0),64);float sh=step(0.001,df);vec3 amb=uAmb*col;vec3 dif=df*col;vec3 spe=sh*sp*vec3(0.8,0.85,0.9);F=vec4(min(amb+dif+spe,vec3(1)),1);}";
    GLuint vs3=c(GL_VERTEX_SHADER,v3d),fs3=c(GL_FRAGMENT_SHADER,f3d); if(!vs3||!fs3) return false;
    shader_3d=glCreateProgram();glAttachShader(shader_3d,vs3);glAttachShader(shader_3d,fs3);glLinkProgram(shader_3d);
    GLint ok3;glGetProgramiv(shader_3d,GL_LINK_STATUS,&ok3);glDeleteShader(vs3);glDeleteShader(fs3);
    return ok3?true:false;
}

void fill_rect(float x,float y,float w,float h,float r,float g,float b){
    verts.push_back(x);verts.push_back(y);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x+w);verts.push_back(y);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x+w);verts.push_back(y+h);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x);verts.push_back(y);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x+w);verts.push_back(y+h);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x);verts.push_back(y+h);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
}

void fill_circle(float cx,float cy,float rad,float r,float g,float b){
    for(int i=0;i<16;i++){float a1=6.283185f*i/16,a2=6.283185f*(i+1)/16,x1=cx+cosf(a1)*rad,y1=cy+sinf(a1)*rad,x2=cx+cosf(a2)*rad,y2=cy+sinf(a2)*rad;
    verts.push_back(cx);verts.push_back(cy);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x1);verts.push_back(y1);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);
    verts.push_back(x2);verts.push_back(y2);verts.push_back(0);verts.push_back(r);verts.push_back(g);verts.push_back(b);}
}

void begin_frame(){
    verts.clear();
    ortho(0,(float)fbW,(float)fbH,0);
}

void end_frame(){
    if(verts.empty()) return;
    glUseProgram(game_shader);
    glUniformMatrix4fv(glGetUniformLocation(game_shader,"uProj"),1,GL_FALSE,proj);
    glBindVertexArray(game_vao); glBindBuffer(GL_ARRAY_BUFFER,game_vbo);
    glBufferData(GL_ARRAY_BUFFER,verts.size()*4,verts.data(),GL_STREAM_DRAW);
    glDrawArrays(GL_TRIANGLES,0,(GLsizei)(verts.size()/6));
}

void on_key_menu(int key);
int menu_hit_test(double mx, double my);
void audio_play_sfx(const char* name);

// ============================================================
// RENDERING: INTRO
// ============================================================
void render_intro() {
    glfwGetFramebufferSize(window, &fbW, &fbH);
    glViewport(0,0,fbW,fbH);
    glClearColor(0.08f,0.08f,0.12f,1);
    glClear(GL_COLOR_BUFFER_BIT);
    begin_frame();
    fill_rect(0,0,(float)fbW,(float)fbH,0.08f,0.08f,0.12f);
    fill_circle((float)fbW/2,(float)fbH/2,80,0.6f,0.5f,0.3f);
    fill_circle((float)fbW/2,(float)fbH/2,75,0.08f,0.08f,0.12f);
    end_frame();

    int fs = std::max(24, std::min(fbW/15, 72));
    if (font_px != fs) bake_font(fs);
    render_text((float)fbW/2, (float)fbH/2-30, "SCHACH", 0.9f,0.8f,0.6f,1,true);
    render_text((float)fbW/2, (float)fbH/2+10, "Ein klassisches Spiel", 0.6f,0.6f,0.7f,1,true);
}

// ============================================================
// RENDERING: MENU
// ============================================================
void render_menu() {
    glViewport(0,0,fbW,fbH);
    glClearColor(0.06f,0.05f,0.08f,1);
    glClear(GL_COLOR_BUFFER_BIT);
    begin_frame();
    fill_rect(0,0,(float)fbW,(float)fbH,0.06f,0.05f,0.08f);
    float m=20; fill_rect(m,m,(float)fbW-m*2,3,0.5f,0.4f,0.25f);
    fill_rect(m,(float)fbH-m-3,(float)fbW-m*2,3,0.5f,0.4f,0.25f);
    fill_rect(m,m,3,(float)fbH-m*2,0.5f,0.4f,0.25f);
    fill_rect((float)fbW-m-3,m,3,(float)fbH-m*2,0.5f,0.4f,0.25f);
    float m2=30; fill_rect(m2,m2,(float)fbW-m2*2,1,0.35f,0.3f,0.18f);
    fill_rect(m2,(float)fbH-m2-1,(float)fbW-m2*2,1,0.35f,0.3f,0.18f);
    fill_rect(m2,m2,1,(float)fbH-m2*2,0.35f,0.3f,0.18f);
    fill_rect((float)fbW-m2-1,m2,1,(float)fbH-m2*2,0.35f,0.3f,0.18f);
    end_frame();

    int fs = std::max(16, std::min(fbW/30, 48));
    int fsm = std::max(28, std::min(fbW/18, 72));
    if (font_px != fs) bake_font(fs);

    // Title
    render_text((float)fbW/2, (float)(fbH*0.12f), "SCHACH", 0.9f,0.8f,0.55f,1,true);

    // Menu buttons
    int bh = std::max(30, std::min(fbH/14, 55));
    int by_start = fbH/2 - (menu_count*bh)/2 - 20;
    int bw = std::min(fbW*3/5, 400);

    int hover = menu_hit_test((float)mouse_x, (float)mouse_y);
    for (int i=0;i<menu_count;i++) {
        int by = by_start + i*bh + i*8;
        begin_frame();
        float r=0.2f,g=0.18f,b=0.25f;
        if (i==menu_sel || i==hover) { r=0.35f; g=0.3f; b=0.45f; }
        fill_rect((float)(fbW/2-bw/2),(float)by,(float)bw,(float)bh,r,g,b);
        fill_rect((float)(fbW/2-bw/2),(float)by,(float)bw,1,0.5f,0.4f,0.25f);
        fill_rect((float)(fbW/2-bw/2),(float)(by+bh-1),(float)bw,1,0.3f,0.25f,0.15f);
        end_frame();
        render_text((float)fbW/2, (float)(by+bh/2-fs/3), menu_items[i], 0.9f,0.9f,0.9f,1,true);
    }

    // Footer
    render_text((float)fbW/2, (float)(fbH-45), "Pfeiltasten: Auswahl  Enter: Bestaetigen", 0.4f,0.4f,0.55f,1,true);
}

// ============================================================
// RENDERING: OPTIONS
// ============================================================
void opt_change(int dir);
int opt_item_count() {
    switch(opt_tab) {
        case OPT_CONTROLS: return 3;
        case OPT_AUDIO: return 6;
        case OPT_GRAPHICS: return 9;
    }
    return 0;
}

const char* opt_val_str(bool b) { return b ? "An" : "Aus"; }

void render_option_item(const char* label, const char* val_str, int item_idx, int x, int y, int w, int h, int fs) {
    begin_frame();
    float r=0.18f,g=0.16f,b=0.22f;
    if (item_idx==opt_item_sel) { r=0.3f; g=0.26f; b=0.38f; }
    fill_rect((float)x,(float)y,(float)w,(float)h,r,g,b);
    fill_rect((float)x,(float)y,(float)w,1,0.4f,0.35f,0.2f);
    fill_rect((float)x,(float)(y+h-1),(float)w,1,0.25f,0.2f,0.12f);
    end_frame();
    render_text((float)(x+8),(float)(y+h/2-fs/3),label,0.85f,0.85f,0.9f,1);
    if (val_str) render_text((float)(x+w-8),(float)(y+h/2-fs/3),val_str,0.7f,0.7f,0.5f,1);
}

void render_tab_controls(int x, int y, int w, int fs) {
    int ih = 28, gap = 4;
    render_option_item("Mausgeschwindigkeit", nullptr, 0, x, y, w, ih, fs);
    char buf[32]; snprintf(buf,sizeof(buf),"%d / 10",opt_mouse_speed);
    render_text((float)(x+w-60),(float)(y+ih/2-fs/3),buf,0.7f,0.7f,0.5f,1);
    y += ih+gap;
    render_option_item("Tastenbelegung (Default)", nullptr, 1, x, y, w, ih, fs);
    render_text((float)(x+w-80),(float)(y+ih/2-fs/3),"Pfeiltasten + Enter",0.5f,0.5f,0.6f,1);
    y += ih+gap;
    render_option_item("Zurueck", nullptr, 2, x, y, w, ih, fs);
}

void render_tab_audio(int x, int y, int w, int fs) {
    int ih = 28, gap = 4;
    render_option_item("Sound", opt_val_str(opt_sound), 0, x, y, w, ih, fs); y += ih+gap;
    char vol[16]; snprintf(vol,sizeof(vol),"%d%%",opt_volume);
    render_option_item("Lautstaerke", vol, 1, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Ausgabegeraet", opt_audio_devices[opt_audio_device], 2, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Mikrofon", opt_val_str(opt_microphone), 3, x, y, w, ih, fs); y += ih+gap;
    char mvol[16]; snprintf(mvol,sizeof(mvol),"%d%%",opt_mic_volume);
    render_option_item("Mikrofon-Lautstaerke", mvol, 4, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Zurueck", nullptr, 5, x, y, w, ih, fs);
}

void render_tab_graphics(int x, int y, int w, int fs) {
    int ih = 28, gap = 4;
    render_option_item("Aufloesung", opt_res_list[opt_resolution], 0, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Vollbild", opt_val_str(opt_fullscreen), 1, x, y, w, ih, fs); y += ih+gap;
    render_option_item("VSync", opt_val_str(opt_vsync), 2, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Anti-Aliasing", opt_aa_list[opt_aa], 3, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Anisotropie", opt_aniso_list[opt_aniso], 4, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Texturdetails", opt_detail_list[opt_tex_detail], 5, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Modelldetails", opt_detail_list[opt_model_detail], 6, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Shaderdetails", opt_detail_list[opt_shader_detail], 7, x, y, w, ih, fs); y += ih+gap;
    render_option_item("Zurueck", nullptr, 8, x, y, w, ih, fs);
}

void render_options() {
    glViewport(0,0,fbW,fbH);
    glClearColor(0.06f,0.05f,0.08f,1);
    glClear(GL_COLOR_BUFFER_BIT);
    begin_frame();
    fill_rect(0,0,(float)fbW,(float)fbH,0.06f,0.05f,0.08f);
    end_frame();

    int fs = std::max(14, std::min(fbW/35, 22));
    int fst = std::max(22, std::min(fbW/22, 36));
    if (font_px != fs) bake_font(fs);

    render_text((float)fbW/2, 18, "OPTIONEN", 0.9f,0.8f,0.55f,fst,true);

    // Tab bar
    int tab_w = (fbW-40)/3;
    int tab_y = 50;
    int tab_h = 28;
    const char* tab_names[] = {"Steuerung", "Sound", "Grafik"};
    for (int i=0;i<3;i++) {
        int tx = 10 + i*(tab_w+10);
        begin_frame();
        if ((int)opt_tab==i) fill_rect((float)tx,(float)tab_y,(float)tab_w,(float)tab_h,0.35f,0.3f,0.45f);
        else fill_rect((float)tx,(float)tab_y,(float)tab_w,(float)tab_h,0.18f,0.16f,0.22f);
        fill_rect((float)tx,(float)tab_y,(float)tab_w,1,0.5f,0.4f,0.25f);
        end_frame();
        render_text((float)(tx+tab_w/2), (float)(tab_y+tab_h/2-fs/3), tab_names[i], 0.9f,0.9f,0.9f,1,true);
    }

    // Items area
    int iy = tab_y + tab_h + 12;
    int iw = std::min(fbW-40, 420);
    int ix = (fbW - iw) / 2;

    if (opt_tab==OPT_CONTROLS) render_tab_controls(ix, iy, iw, fs);
    else if (opt_tab==OPT_AUDIO) render_tab_audio(ix, iy, iw, fs);
    else if (opt_tab==OPT_GRAPHICS) render_tab_graphics(ix, iy, iw, fs);

    render_text((float)fbW/2, (float)(fbH-22), "Tab: L/R  Item: UP/DOWN  Wert: L/R  ESC: Zurueck", 0.4f,0.4f,0.55f,1,true);
}

void opt_change(int dir) {
    int cnt = opt_item_count();
    switch(opt_tab) {
        case OPT_CONTROLS: {
            switch(opt_item_sel) {
                case 0: opt_mouse_speed = std::max(1,std::min(10,opt_mouse_speed+dir)); break;
                case 1: break; // Tastenbelegung (Anzeige)
                case 2: if (dir>0) mode=MENU; break;
            }
            break;
        }
        case OPT_AUDIO: {
            switch(opt_item_sel) {
                case 0: opt_sound = !opt_sound; break;
                case 1: opt_volume = std::max(0,std::min(100,opt_volume+dir*10)); break;
                case 2: opt_audio_device = (opt_audio_device+dir+opt_audio_dev_count)%opt_audio_dev_count; break;
                case 3: opt_microphone = !opt_microphone; break;
                case 4: opt_mic_volume = std::max(0,std::min(100,opt_mic_volume+dir*10)); break;
                case 5: if (dir>0) mode=MENU; break;
            }
            break;
        }
        case OPT_GRAPHICS: {
            int res = opt_resolution;
            switch(opt_item_sel) {
                case 0: opt_resolution = (opt_resolution+dir+opt_res_count)%opt_res_count; break;
                case 1: opt_fullscreen = !opt_fullscreen; break;
                case 2: opt_vsync = !opt_vsync; break;
                case 3: opt_aa = (opt_aa+dir+opt_aa_count)%opt_aa_count; break;
                case 4: opt_aniso = (opt_aniso+dir+opt_aniso_count)%opt_aniso_count; break;
                case 5: opt_tex_detail = std::max(0,std::min(2,opt_tex_detail+dir)); break;
                case 6: opt_model_detail = std::max(0,std::min(2,opt_model_detail+dir)); break;
                case 7: opt_shader_detail = std::max(0,std::min(2,opt_shader_detail+dir)); break;
                case 8: if (dir>0) mode=MENU; break;
            }
            break;
        }
    }
}

// ============================================================
// RENDERING: CHESS GAME
// ============================================================
extern bool enable_3d;
extern bool cam_dragging;
extern double cam_drag_x,cam_drag_y;
extern float cam_theta,cam_phi;
void render_3d();
void cam_update();
int pick_square(double mx,double my);
void handle_click(double mx,double my);
void render_piece(float cx,float cy,float s,Piece p,Color c){
    float pr,pg,pb;
    if(c==WHITE){pr=0.95f;pg=0.93f;pb=0.85f;}else{pr=0.12f;pg=0.12f;pb=0.14f;}
    float r=s*0.5f;
    switch(p){
        case P:fill_circle(cx,cy,r*0.45f,pr,pg,pb);break;
        case R:fill_rect(cx-r*0.5f,cy-r*0.35f,r,r*0.65f,pr,pg,pb);fill_rect(cx-r*0.4f,cy-r*0.55f,r*0.22f,r*0.2f,pr,pg,pb);fill_rect(cx+r*0.18f,cy-r*0.55f,r*0.22f,r*0.2f,pr,pg,pb);break;
        case N:fill_rect(cx-r*0.35f,cy-r*0.45f,r*0.7f,r*0.9f,pr,pg,pb);fill_circle(cx+r*0.2f,cy-r*0.25f,r*0.3f,pr,pg,pb);break;
        case B:fill_circle(cx,cy-r*0.1f,r*0.5f,pr,pg,pb);fill_circle(cx,cy,r*0.15f,0.8f,0.8f,0.8f);break;
        case Q:fill_circle(cx,cy,r*0.55f,pr,pg,pb);fill_circle(cx,cy-r*0.65f,r*0.15f,pr,pg,pb);fill_circle(cx-r*0.25f,cy-r*0.6f,r*0.12f,pr,pg,pb);fill_circle(cx+r*0.25f,cy-r*0.6f,r*0.12f,pr,pg,pb);break;
        case K:fill_circle(cx,cy,r*0.55f,pr,pg,pb);fill_rect(cx-r*0.1f,cy-r*0.65f,r*0.2f,r*0.55f,pr,pg,pb);fill_rect(cx-r*0.25f,cy-r*0.42f,r*0.5f,r*0.2f,pr,pg,pb);break;
        default:break;
    }
}

void render_game() {
    if(enable_3d){
        render_3d();
    }else{
        glViewport(0,0,fbW,fbH);
        glClearColor(0.08f,0.08f,0.12f,1);
        glClear(GL_COLOR_BUFFER_BIT);
    }

    int sq_size = std::min((fbW-60)/8,(fbH-60)/8);
    if (sq_size<20) sq_size=20;
    int board_px = sq_size*8;
    bool wide = (float)fbW/fbH > 1.3f;

    int bx, by, panel_x, panel_y, panel_w, panel_h;
    if (wide) {
        bx = BOARD_OFF; by = (fbH-board_px)/2;
        panel_x = board_px+BOARD_OFF*2+10; panel_y = 10;
        panel_w = fbW-panel_x-10; panel_h = fbH-20;
        if (panel_w < 100) { bx = (fbW-board_px)/2; panel_x = 0; }
    } else {
        bx = (fbW-board_px)/2; by = BOARD_OFF;
        panel_x = 10; panel_y = board_px+BOARD_OFF*2+10;
        panel_w = fbW-20; panel_h = fbH-panel_y-10;
    }

    if(!enable_3d){
        begin_frame();
        fill_rect(0,0,(float)fbW,(float)fbH,0.08f,0.08f,0.12f);
        fill_rect((float)(bx-4),(float)(by-4),(float)(board_px+8),(float)(board_px+8),0.12f,0.12f,0.16f);
        for (int r=0;r<8;r++) for (int f=0;f<8;f++) {
            float x=(float)(bx+f*sq_size),y=(float)(by+r*sq_size);
            bool light=(f+r)%2==0;
            float c=light?0.88f:0.55f;
            fill_rect(x,y,(float)sq_size,(float)sq_size,c,c,(light?0.82f:0.45f));
        }
        if (last_from>=0) {
            fill_rect((float)(bx+file_of(last_from)*sq_size),(float)(by+rank_of(last_from)*sq_size),(float)sq_size,(float)sq_size,0.45f,0.55f,0.25f);
            fill_rect((float)(bx+file_of(last_to)*sq_size),(float)(by+rank_of(last_to)*sq_size),(float)sq_size,(float)sq_size,0.45f,0.55f,0.25f);
        }
        if (sel>=0) fill_rect((float)(bx+file_of(sel)*sq_size),(float)(by+rank_of(sel)*sq_size),(float)sq_size,(float)sq_size,0.35f,0.65f,0.35f);
        for (int m:legal_moves) fill_circle((float)(bx+file_of(m)*sq_size+sq_size/2),(float)(by+rank_of(m)*sq_size+sq_size/2),sq_size*0.12f,0.2f,0.9f,0.2f);
        for (int r=0;r<8;r++) for (int f=0;f<8;f++) {
            int idx=::sq(f,r);
            if (board.p[idx]!=EMPTY) render_piece((float)(bx+f*sq_size+sq_size/2),(float)(by+r*sq_size+sq_size/2),(float)sq_size,board.p[idx],board.c[idx]);
        }
        end_frame();
    }

    // Text overlay
    int fs = std::max(14, std::min(fbW/35, 32));
    if (mode==GAME && font_px != fs) bake_font(fs);

    int tx = wide ? panel_x : panel_x+5;
    int ty = wide ? panel_y+5 : panel_y+5;

    render_text((float)tx,(float)ty,status_msg.c_str(),1,1,1,1);
    char buf[128];
    snprintf(buf,128,"Zug %d",fullmove);
    render_text((float)tx,(float)(ty+fs+5),buf,0.8f,0.8f,0.8f,1);
    if (net_game && net_state==NET_CONNECTED) {
        char lbuf[64]; snprintf(lbuf,64,"%s (%d)",net_my_name,rating_get(net_my_name));
        render_text((float)tx,(float)(ty+fs*2+5),lbuf,0.7f,0.9f,0.7f,1);
        char rbuf[64]; snprintf(rbuf,64,"%s (%d)",net_opp_name[0]?net_opp_name:"???",rating_get(net_opp_name));
        render_text((float)tx,(float)(ty+fs*3+5),rbuf,0.9f,0.7f,0.7f,1);
    }

    if (wide) ty += 50; else ty += fs*4;

    // Captured
    const char* pn = "?BSLTDK";
    if (num_cap_w>0||num_cap_b>0) {
        render_text((float)tx,(float)ty,"Geschlagen:",0.6f,0.6f,0.8f,1);
        ty += fs+3;
        int ox=tx;
        for (int i=0;i<num_cap_w;i++) {
            char pc[2]={pn[captured_white[i]],0};
            render_text((float)tx,(float)ty,pc,0.9f,0.6f,0.6f,1); tx+=(fs/2+2);
        }
        if (wide) { tx = panel_x; } else { tx = ox; }
        ty += fs+2;
        for (int i=0;i<num_cap_b;i++) {
            char pc[2]={pn[captured_black[i]],0};
            render_text((float)tx,(float)ty,pc,0.6f,0.6f,1,1); tx+=(fs/2+2);
        }
    }

    if (wide) { tx = panel_x; ty = panel_h-110; } else { tx = panel_x+5; ty = fbH - fbH/5 + 10; }
    if (ty < 0) ty = 10;

    render_text((float)tx,(float)ty,"ESC: Menue",0.4f,0.4f,0.65f,1);
    render_text((float)tx,(float)(ty+fs+2),"R: Neustart",0.4f,0.4f,0.65f,1);

    if (show_ai_thinking && turn==ai_side && ai_enabled) {
        render_text((float)fbW/2,(float)fbH-30,"KI denkt...",0.7f,0.7f,1.0f,1,true);
    }

    // Promotion dialog
    if (promoting) {
        int pf = file_of(promo_to), pr = rank_of(promo_to);
        float pcx = (float)(bx+pf*sq_size+sq_size/2);
        float pcy = (float)(by+pr*sq_size+sq_size/2);
        float py = (pr==0) ? pcy+sq_size*0.7f : pcy-sq_size*0.7f-sq_size*0.4f;
        float px = pcx - sq_size*0.8f;
        Piece choices[4] = {Q,R,B,N};
        begin_frame();
        fill_rect(px-10,py-5,sq_size*2.4f+20,sq_size*0.55f+10,0.15f,0.15f,0.2f);
        fill_rect(px-8,py-3,sq_size*2.4f+16,sq_size*0.55f+6,0.5f,0.4f,0.25f);
        fill_rect(px-6,py-1,sq_size*2.4f+12,sq_size*0.55f+2,0.06f,0.05f,0.08f);
        Color promo_col = (pr==0)?WHITE:BLACK;
        for (int i=0;i<4;i++) {
            float cx = px + i*sq_size*0.55f + sq_size*0.3f;
            float cy = py + sq_size*0.2f;
            fill_rect(cx-sq_size*0.22f,cy-sq_size*0.18f,sq_size*0.44f,sq_size*0.36f,0.25f,0.22f,0.3f);
            fill_rect(cx-sq_size*0.22f,cy-sq_size*0.18f,sq_size*0.44f,1,0.5f,0.4f,0.25f);
            fill_rect(cx-sq_size*0.22f,(cy+sq_size*0.18f-1),sq_size*0.44f,1,0.3f,0.25f,0.15f);
            render_piece(cx,cy+2,sq_size*0.3f,choices[i],promo_col);
        }
        end_frame();
    }

    // Game over overlay
    if (game_over) {
        begin_frame();
        fill_rect(0,0,(float)fbW,(float)fbH,0.02f,0.02f,0.04f);
        end_frame();
        int gfs = std::max(28, std::min(fbW/20, 64));
        if (font_px != gfs) bake_font(gfs);
        render_text((float)fbW/2,(float)fbH/2-30,status_msg.c_str(),1,1,0.8f,1,true);
        if (net_game && net_rating_received) {
            char buf[96]; snprintf(buf,sizeof(buf),"%s: %d  |  %s: %d",net_my_name,net_rating_winner,net_opp_name,net_rating_loser);
            render_text((float)fbW/2,(float)fbH/2+5,buf,0.8f,0.8f,0.6f,1,true);
        }
        render_text((float)fbW/2,(float)fbH/2+25,"Klicke zum Neustart",0.7f,0.7f,0.9f,1,true);
    }
}

// ============================================================
// GAME INPUT
// ============================================================
void on_square_click(int sq_idx) {
    if (game_over) return;
    if (promoting) return;
    if (net_game && !net_my_turn) return;
    if (ai_enabled && turn==ai_side) return;

    if (sel==-1) {
        if (board.p[sq_idx]!=EMPTY&&board.c[sq_idx]==turn) {
            sel=sq_idx; legal_moves.clear();
            generate_moves_for(sel,legal_moves,board,false,turn);
            std::vector<int> filt;
            for (int m:legal_moves) if (is_legal_move(sel,m,board,turn)) filt.push_back(m);
            legal_moves=filt;
        }
    } else {
        bool legal=false;
        for (int m:legal_moves) if (m==sq_idx) { legal=true; break; }
        if (legal) {
            if (board.p[sel]==P&&(rank_of(sq_idx)==0||rank_of(sq_idx)==7)) {
                promo_from = sel; promo_to = sq_idx; promoting = true;
                return;
            }
            do_move(sel,sq_idx);
            if (ai_enabled && turn==ai_side && !game_over) {
                show_ai_thinking = true;
            }
        } else if (board.p[sq_idx]!=EMPTY&&board.c[sq_idx]==turn) {
            sel=sq_idx; legal_moves.clear();
            generate_moves_for(sel,legal_moves,board,false,turn);
            std::vector<int> filt;
            for (int m:legal_moves) if (is_legal_move(sel,m,board,turn)) filt.push_back(m);
            legal_moves=filt;
        } else { sel=-1; legal_moves.clear(); }
    }
}

int menu_hit_test(double mx, double my) {
    int bh = std::max(30, std::min(fbH/14, 55));
    int by_start = fbH/2 - (menu_count*bh)/2 - 20;
    int bw = std::min(fbW*3/5, 400);
    for (int i=0;i<menu_count;i++) {
        int by = by_start + i*bh + i*8;
        int x0 = fbW/2 - bw/2, y0 = by, x1 = x0 + bw, y1 = y0 + bh;
        if (mx>=x0 && mx<x1 && my>=y0 && my<y1) return i;
    }
    return -1;
}

void on_mouse_button(GLFWwindow*,int button,int action,int){
    if(button==GLFW_MOUSE_BUTTON_LEFT&&action==GLFW_PRESS){
        handle_click(mouse_x,mouse_y);
    }
    if(button==GLFW_MOUSE_BUTTON_RIGHT&&action==GLFW_PRESS&&enable_3d&&mode==GAME){
        cam_dragging=true;cam_drag_x=mouse_x;cam_drag_y=mouse_y;
    }
    if(action==GLFW_RELEASE&&cam_dragging)cam_dragging=false;
}
void handle_click(double mx,double my){
    int ix=(int)mx,iy=(int)my;
    if (mode==MENU) {
        if (menu_page==MENU_MAIN) {
            int hit = menu_hit_test(mx,my);
            if (hit>=0) { menu_sel=hit; on_key_menu(GLFW_KEY_ENTER); }
        } else if (menu_page==MENU_NETWORK) {
            net_editing_name=false;
            int bh = std::max(30, std::min(fbH/14, 55));
            int by_start = fbH/2 - (net_menu_count*bh)/2 - 20;
            int bw = std::min(fbW*3/5, 400);
            for (int i=0;i<net_menu_count;i++) {
                int by = by_start + i*bh + i*8;
                if (mx>=fbW/2-bw/2 && mx<fbW/2+bw/2 && my>=by && my<by+bh) {
                    net_menu_sel=i; on_key_menu(GLFW_KEY_ENTER); break;
                }
            }
        }
        return;
    }
    if (mode==OPTIONS) {
        // Tab clicks
        int tab_w = (fbW-40)/3;
        for (int i=0;i<3;i++) {
            int tx = 10 + i*(tab_w+10);
            if (mx>=tx && mx<tx+tab_w && my>=50 && my<50+28) {
                opt_tab=(OptTab)i; opt_item_sel=0; return;
            }
        }
        // Item clicks
        int iw = std::min(fbW-40, 420);
        int ix = (fbW - iw) / 2;
        int iy = 50+28+12;
        int cnt = opt_item_count();
        for (int i=0;i<cnt;i++) {
            int item_h = 32;
            if (mx>=ix && mx<ix+iw && my>=iy+i*item_h && my<iy+i*item_h+item_h) {
                opt_item_sel=i;
                // "Zurueck" items are always last
                if (i==cnt-1) { mode=MENU; return; }
                opt_change(1);
                return;
            }
        }
        return;
    }
    if (mode!=GAME) return;

    // Promotion dialog click
    if (promoting) {
        int sq_size = std::min((fbW-60)/8,(fbH-60)/8);
        if (sq_size<20) sq_size=20;
        int board_px = sq_size*8;
        bool wide = (float)fbW/fbH > 1.3f;
        int bx = wide?BOARD_OFF:(fbW-board_px)/2;
        int by = wide?(fbH-board_px)/2:BOARD_OFF;
        int pf = file_of(promo_to), pr = rank_of(promo_to);
        float pcx = (float)(bx+pf*sq_size+sq_size/2);
        float pcy = (float)(by+pr*sq_size+sq_size/2);
        float py = (pr==0) ? pcy+sq_size*0.7f : pcy-sq_size*0.7f - sq_size*0.4f;
        float px = pcx - sq_size*0.8f;
        Piece choices[4] = {Q,R,B,N};
        for (int i=0;i<4;i++) {
            float cx = px + i*sq_size*0.55f + sq_size*0.3f;
            float cy = py + sq_size*0.2f;
            if (mx>=cx-sq_size*0.25f && mx<cx+sq_size*0.25f && my>=cy-sq_size*0.2f && my<cy+sq_size*0.2f) {
                do_move(promo_from, promo_to, choices[i]);
                promoting = false;
                return;
            }
        }
        return;
    }

    // Game over overlay: click = restart
    if (game_over) {
        if (mode==GAME) {
            if (net_game) { net_cleanup(); mode=MENU; menu_page=MENU_MAIN; return; }
            init_board(); ai_timer=0; show_ai_thinking=false; game_over=false;
            if (ai_enabled) status_msg="Weiss ist am Zug";
        }
        return;
    }

    if(enable_3d){
        int sq=pick_square((double)ix,(double)iy);
        if(sq>=0)on_square_click(sq);
    }else{
        int sq_size = std::min((fbW-60)/8,(fbH-60)/8);
        if (sq_size<20) sq_size=20;
        int board_px = sq_size*8;
        bool wide = (float)fbW/fbH > 1.3f;
        int bx = wide?BOARD_OFF:(fbW-board_px)/2;
        int by = wide?(fbH-board_px)/2:BOARD_OFF;
        int fx=(ix-bx)/sq_size, ry=(iy-by)/sq_size;
        if (fx>=0&&fx<8&&ry>=0&&ry<8) on_square_click(::sq(fx,ry));
    }
}

void on_key_menu(int key) {
    if (menu_page == MENU_NETWORK) {
        if (net_editing_name) {
            if (key==GLFW_KEY_ENTER||key==GLFW_KEY_ESCAPE) { net_editing_name=false; }
            else if (key==GLFW_KEY_BACKSPACE) {
                int len=(int)strlen(net_my_name);
                if(len>0) net_my_name[len-1]=0;
            }
            return;
        }
        if (key==GLFW_KEY_UP) { net_menu_sel=(net_menu_sel-1+net_menu_count)%net_menu_count; }
        else if (key==GLFW_KEY_DOWN) { net_menu_sel=(net_menu_sel+1)%net_menu_count; }
        else if (key==GLFW_KEY_ENTER) {
            if (net_menu_sel==0) { // name edit
                net_editing_name=true;
            } else if (net_menu_sel==1) { // hosten
                net_start_host();
            } else if (net_menu_sel==2) { // beitreten
                menu_page = MENU_NET_IP; net_ip_buf[0]=0; net_ip_len=0;
            } else if (net_menu_sel==3) { // rangliste
                ratings_load(); menu_page=MENU_RANKING;
            } else if (net_menu_sel==4) { // zurueck
                menu_page = MENU_MAIN; net_cancel();
            }
        }
        else if (key==GLFW_KEY_ESCAPE) { menu_page=MENU_MAIN; net_cancel(); }
        return;
    }
    if (menu_page == MENU_NET_IP) {
        if (key==GLFW_KEY_ENTER) {
            if (net_ip_len>0) { net_start_connect(); menu_page=MENU_NETWORK; }
        }
        else if (key==GLFW_KEY_ESCAPE) { menu_page=MENU_NETWORK; }
        else if (key==GLFW_KEY_BACKSPACE) { if(net_ip_len>0){net_ip_buf[--net_ip_len]=0;} }
        return;
    }
    if (menu_page == MENU_RANKING) {
        if (key==GLFW_KEY_ESCAPE) { menu_page=MENU_NETWORK; }
        return;
    }
    // Main menu
    if (key==GLFW_KEY_UP) { menu_sel=(menu_sel-1+menu_count)%menu_count; }
    else if (key==GLFW_KEY_DOWN) { menu_sel=(menu_sel+1)%menu_count; }
    else if (key==GLFW_KEY_ENTER) {
        if (menu_sel==0) { // 1 Spieler vs Computer
            init_board(); mode=GAME; ai_enabled=true; ai_timer=0; show_ai_thinking=false;
            status_msg="Weiss ist am Zug";
        } else if (menu_sel==1) { // 2 Spieler
            init_board(); mode=GAME; ai_enabled=false; show_ai_thinking=false;
            status_msg="Weiss ist am Zug";
        } else if (menu_sel==2) { // Netzwerk
            menu_page=MENU_NETWORK; net_menu_sel=0;
        } else if (menu_sel==3) { // Optionen
            mode=OPTIONS; opt_tab=OPT_CONTROLS; opt_item_sel=0;
        } else if (menu_sel==4) { // Beenden
            glfwSetWindowShouldClose(window,1);
        }
    }
}

void on_key_options(int key) {
    if (key==GLFW_KEY_ESCAPE) { mode=MENU; return; }
    if (key==GLFW_KEY_LEFT) {
        if (opt_item_sel==0) { opt_tab=(OptTab)(((int)opt_tab-1+3)%3); opt_item_sel=0; }
        else opt_change(-1);
        return;
    }
    if (key==GLFW_KEY_RIGHT) {
        if (opt_item_sel==0) { opt_tab=(OptTab)(((int)opt_tab+1)%3); opt_item_sel=0; }
        else opt_change(1);
        return;
    }
    int cnt = opt_item_count();
    if (key==GLFW_KEY_UP) { opt_item_sel=(opt_item_sel-1+cnt)%cnt; }
    else if (key==GLFW_KEY_DOWN) { opt_item_sel=(opt_item_sel+1)%cnt; }
    else if (key==GLFW_KEY_ENTER) { opt_change(1); }
}

void on_key_game(int key) {
    if (key==GLFW_KEY_ESCAPE) {
        if (net_game) { net_cleanup(); mode=MENU; game_over=false; return; }
        mode=MENU; game_over=false; return;
    }
    if (key==GLFW_KEY_R) {
        if (net_game) return;
        init_board(); ai_timer=0; show_ai_thinking=false; game_over=false;
        status_msg="Weiss ist am Zug";
    }
    if (promoting) {
        if (key=='D'||key=='d') { do_move(promo_from,promo_to,Q); promoting=false; return; }
        if (key=='T'||key=='t') { do_move(promo_from,promo_to,R); promoting=false; return; }
        if (key=='L'||key=='l') { do_move(promo_from,promo_to,B); promoting=false; return; }
        if (key=='S'||key=='s') { do_move(promo_from,promo_to,N); promoting=false; return; }
        return;
    }
}

void on_key(GLFWwindow* win,int key,int,int action,int mods) {
    if (action!=GLFW_PRESS) return;
    // Ctrl+V paste in IP entry
    if (mode==MENU && menu_page==MENU_NET_IP && key==GLFW_KEY_V && (mods&GLFW_MOD_CONTROL)) {
        const char* clip = glfwGetClipboardString(win);
        if (clip) {
            int len = (int)strlen(clip);
            for (int i=0;i<len && net_ip_len<30;i++) {
                char c = clip[i];
                if (c=='.'||(c>='0'&&c<='9')) net_ip_buf[net_ip_len++]=c;
            }
            net_ip_buf[net_ip_len]=0;
        }
        return;
    }
    if (mode==MENU) on_key_menu(key);
    else if (mode==OPTIONS) on_key_options(key);
    else if (mode==GAME) on_key_game(key);
}

void on_cursor(GLFWwindow*,double x,double y){
    mouse_x=x;mouse_y=y;
    if(cam_dragging){
        double dx=x-cam_drag_x,dy=y-cam_drag_y;
        cam_theta-=dx*0.005f;cam_phi+=dy*0.005f;
        if(cam_phi>1.5f)cam_phi=1.5f;
        if(cam_phi<-0.1f)cam_phi=-0.1f;
        cam_drag_x=x;cam_drag_y=y;
        cam_update();
    }
}

void on_char(GLFWwindow*,unsigned int cp) {
    if (mode!=MENU) return;
    if (menu_page==MENU_NET_IP && (cp=='.'||(cp>='0'&&cp<='9'))) {
        if (net_ip_len<30) { net_ip_buf[net_ip_len++]=(char)cp; net_ip_buf[net_ip_len]=0; }
    }
    if (menu_page==MENU_NETWORK && net_editing_name) {
        if (cp>=32&&cp<127) {
            int len=(int)strlen(net_my_name);
            if (len<30) { net_my_name[len]=(char)cp; net_my_name[len+1]=0; }
        }
    }
}

// ============================================================
// AUDIO SYSTEM (Windows PlaySound)
// ============================================================
#pragma comment(lib, "winmm.lib")
const char* SOUND_DIR = "sounds\\";
GameMode prev_mode = INTRO;

bool file_exists(const char* path) {
    FILE* f = fopen(path,"rb"); if(!f) return false; fclose(f); return true;
}

void audio_play_music(const char* name) {
    if (!opt_sound) return;
    char path[260]; snprintf(path,sizeof(path),"%s%s",SOUND_DIR,name);
    if (file_exists(path)) PlaySoundA(path,NULL,SND_FILENAME|SND_LOOP|SND_ASYNC);
}

void audio_play_sfx(const char* name) {
    if (!opt_sound) return;
    char path[260]; snprintf(path,sizeof(path),"%s%s",SOUND_DIR,name);
    if (file_exists(path)) PlaySoundA(path,NULL,SND_FILENAME|SND_ASYNC|SND_NOSTOP);
}

void audio_stop() { PlaySoundA(NULL,NULL,0); }

void audio_update(GameMode new_mode) {
    if (new_mode==prev_mode) return;
    prev_mode = new_mode;
    audio_stop();
    if (new_mode==MENU) audio_play_music("menu.wav");
    else if (new_mode==GAME) audio_play_music("game.wav");
}

// ============================================================
// NETWORK SYSTEM (Winsock TCP)
// ============================================================
void net_cleanup() {
    if (net_sock != INVALID_SOCKET) { closesocket(net_sock); net_sock = INVALID_SOCKET; }
    if (net_listen != INVALID_SOCKET) { closesocket(net_listen); net_listen = INVALID_SOCKET; }
    net_state = NET_IDLE; net_game = false;
}

void net_start_host() {
    net_cleanup();
    net_listen = socket(AF_INET, SOCK_STREAM, 0);
    if (net_listen == INVALID_SOCKET) { net_state=NET_ERROR; snprintf(net_info,64,"Socket-Fehler"); return; }
    sockaddr_in addr;
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_port = htons(net_port);
    if (bind(net_listen,(sockaddr*)&addr,sizeof(addr))!=0) {
        closesocket(net_listen); net_listen=INVALID_SOCKET;
        net_state=NET_ERROR; snprintf(net_info,64,"Bind-Fehler (Port %d belegt)",net_port); return;
    }
    listen(net_listen,1);
    u_long nonblock=1; ioctlsocket(net_listen,FIONBIO,&nonblock);
    // Get local IP
    char hostname[256]; gethostname(hostname,256);
    struct hostent* he = gethostbyname(hostname);
    char ips[128]="";
    if(he){
        for(int i=0;he->h_addr_list[i];i++){
            if(i>0) strcat(ips,"  ");
            strcat(ips,inet_ntoa(*(struct in_addr*)he->h_addr_list[i]));
            if(strlen(ips)>100) break;
        }
    }
    // Extract first IP for display and clipboard
    char first_ip[32]="?";
    if(ips[0]){char* sp=strchr(ips,' ');if(sp)*sp=0;strncpy(first_ip,ips,31);first_ip[31]=0;}
    net_state=NET_CONNECTING;
    snprintf(net_info,sizeof(net_info),"Host: %s:%d | IP: %s (in Zwischenablage!)",hostname,net_port,first_ip);
    net_my_turn=true;
    // Copy first IP to clipboard via GLFW
    if(first_ip[0]&&first_ip[0]!='?'&&window) glfwSetClipboardString(window,first_ip);
}

void net_start_connect() {
    net_cleanup();
    net_sock=socket(AF_INET,SOCK_STREAM,0);
    if(net_sock==INVALID_SOCKET){net_state=NET_ERROR;snprintf(net_info,64,"Socket-Fehler");return;}
    sockaddr_in addr;
    addr.sin_family=AF_INET;
    addr.sin_addr.s_addr=inet_addr(net_ip_buf);
    addr.sin_port=htons(net_port);
    u_long nonblock=1; ioctlsocket(net_sock,FIONBIO,&nonblock);
    connect(net_sock,(sockaddr*)&addr,sizeof(addr));
    net_state=NET_CONNECTING;
    snprintf(net_info,64,"Verbinde mit %s...",net_ip_buf);
    net_my_turn=false;
}

void net_poll() {
    if (net_state==NET_IDLE||net_state==NET_ERROR) return;

    // Host: try accept
    if (net_listen!=INVALID_SOCKET) {
        sockaddr_in cl; int len=sizeof(cl);
        SOCKET s=accept(net_listen,(sockaddr*)&cl,&len);
        if(s!=INVALID_SOCKET){
            closesocket(net_listen); net_listen=INVALID_SOCKET;
            net_sock=s; u_long nonblock=1; ioctlsocket(net_sock,FIONBIO,&nonblock);
            ratings_load(); net_opp_name[0]=0; net_rating_received=false;
            char msg[64]; snprintf(msg,64,"NAME:%s\n",net_my_name);
            send(net_sock,msg,(int)strlen(msg),0);
            net_state=NET_CONNECTED; net_game=true;
            snprintf(net_info,64,"Verbunden! (Host)");
            mode=GAME; init_board(); game_over=false; ai_enabled=false;
            status_msg="Weiss ist am Zug (du)";
            audio_update(GAME);
        }
        return;
    }

    if(net_sock==INVALID_SOCKET) return;

    // Check non-blocking connect completion
    if(net_state==NET_CONNECTING){
        fd_set w; FD_ZERO(&w); FD_SET(net_sock,&w);
        timeval tv={0,0};
        if(select(0,NULL,&w,NULL,&tv)>0){
            int err=0; int elen=sizeof(err);
            getsockopt(net_sock,SOL_SOCKET,SO_ERROR,(char*)&err,&elen);
            if(err==0){
                net_opp_name[0]=0; net_rating_received=false; net_recv_len=0;
                char msg[64]; snprintf(msg,64,"NAME:%s\n",net_my_name);
                send(net_sock,msg,(int)strlen(msg),0);
                net_state=NET_CONNECTED; net_game=true;
                snprintf(net_info,64,"Verbunden! (Client)");
                mode=GAME; init_board(); game_over=false; ai_enabled=false;
                status_msg="Schwarz ist am Zug (warte...)";
                audio_update(GAME);
            }else{
                net_state=NET_ERROR;
                snprintf(net_info,64,"Fehler: %d",err);
            }
        }
        return;
    }

    // Receive data with buffered line processing
    if(net_state==NET_CONNECTED&&net_sock!=INVALID_SOCKET){
        char buf[256]; int ret=recv(net_sock,buf,255,0);
        if(ret>0){
            buf[ret]=0;
            int remain=(int)(sizeof(net_recv_buf)-net_recv_len-1);
            if(ret<remain){memcpy(net_recv_buf+net_recv_len,buf,ret);net_recv_len+=ret;net_recv_buf[net_recv_len]=0;}
            // Process complete lines
            char* ls=net_recv_buf;
            while(1){
                char* nl=strchr(ls,'\n'); if(!nl) break;
                *nl=0; char* cr=strchr(ls,'\r'); if(cr)*cr=0;
                // Process line
                if(strncmp(ls,"NAME:",5)==0){
                    strncpy(net_opp_name,ls+5,31);net_opp_name[31]=0;
                }else if(strncmp(ls,"RATING:",7)==0){
                    sscanf(ls+7,"%d:%d",&net_rating_winner,&net_rating_loser);
                    net_rating_received=true;
                }else{
                    int f=-1,t=-1; char pr=0;
                    if(sscanf(ls,"%d %d %c",&f,&t,&pr)>=2&&f>=0&&f<64&&t>=0&&t<64){
                        Piece pp=Q;
                        if(pr){char up=(char)toupper(pr);pp=(up=='R')?R:(up=='B')?B:(up=='N')?N:Q;}
                        net_from_network=true;
                        do_move(f,t,pp);
                        net_from_network=false;
                        net_my_turn=true;
                    }
                }
                ls=nl+1;
            }
            // Move remaining to front
            if(ls>net_recv_buf&&ls<net_recv_buf+net_recv_len){
                int rem=net_recv_len-(int)(ls-net_recv_buf);
                memmove(net_recv_buf,ls,rem);net_recv_len=rem;
            }else if(ls>=net_recv_buf+net_recv_len){net_recv_len=0;}
            net_recv_buf[net_recv_len]=0;
        }else if(ret==0){
            net_state=NET_ERROR;
            snprintf(net_info,64,"Verbindung getrennt!");
            net_cleanup();
        }
    }
}

void net_send_move(int from, int to, Piece promo) {
    if(net_state!=NET_CONNECTED||net_sock==INVALID_SOCKET) return;
    char buf[32];
    if(promo==Q||promo==R||promo==B||promo==N){
        char pc=(promo==Q)?'Q':(promo==R)?'R':(promo==B)?'B':'N';
        snprintf(buf,32,"%d %d %c\n",from,to,pc);
    }else snprintf(buf,32,"%d %d\n",from,to);
    send(net_sock,buf,(int)strlen(buf),0);
    net_my_turn=false;
}

void net_cancel() { net_cleanup(); net_state=NET_IDLE; menu_page=MENU_MAIN; }

// ============================================================
// NETWORK UI
// ============================================================

void render_network_menu() {
    glViewport(0,0,fbW,fbH);
    glClearColor(0.06f,0.05f,0.08f,1);
    glClear(GL_COLOR_BUFFER_BIT);
    begin_frame(); fill_rect(0,0,(float)fbW,(float)fbH,0.06f,0.05f,0.08f); end_frame();

    int fs = std::max(16, std::min(fbW/30, 48));
    int fsm = std::max(28, std::min(fbW/18, 72));
    if (font_px != fs) bake_font(fs);

    render_text((float)fbW/2,(float)(fbH*0.12f),"NETZWERK",0.9f,0.8f,0.55f,1,true);

    if (menu_page == MENU_NETWORK) {
        int bh = std::max(30, std::min(fbH/14, 55));
        int by_start = fbH/2 - (net_menu_count*bh)/2 - 20;
        int bw = std::min(fbW*3/5, 400);
        int hover = -1; double mx=mouse_x, my=mouse_y;
        for (int i=0;i<net_menu_count;i++) {
            int by = by_start + i*bh + i*8;
            if (mx>=fbW/2-bw/2 && mx<fbW/2+bw/2 && my>=by && my<by+bh) { hover=i; break; }
        }
        for (int i=0;i<net_menu_count;i++) {
            int by = by_start + i*bh + i*8;
            begin_frame();
            float r=0.2f,g=0.18f,b=0.25f;
            if (i==net_menu_sel || i==hover) { r=0.35f; g=0.3f; b=0.45f; }
            if (i==0 && net_editing_name) { r=0.4f; g=0.35f; b=0.5f; } // editing highlight
            fill_rect((float)(fbW/2-bw/2),(float)by,(float)bw,(float)bh,r,g,b);
            fill_rect((float)(fbW/2-bw/2),(float)by,(float)bw,1,0.5f,0.4f,0.25f);
            fill_rect((float)(fbW/2-bw/2),(float)(by+bh-1),(float)bw,1,0.3f,0.25f,0.15f);
            end_frame();
            if (i==0) {
                char name_label[64];
                snprintf(name_label,64,"Name: %s%s",net_my_name,net_editing_name?"_":"");
                render_text((float)fbW/2,(float)(by+bh/2-fs/3),name_label,0.9f,0.9f,0.9f,1,true);
            } else if (i==3) {
                char rl[64]; snprintf(rl,64,"Rangliste (%d)",rating_count);
                render_text((float)fbW/2,(float)(by+bh/2-fs/3),rl,0.9f,0.9f,0.9f,1,true);
            } else {
                render_text((float)fbW/2,(float)(by+bh/2-fs/3),net_menu_items[i],0.9f,0.9f,0.9f,1,true);
            }
        }
    }

    if (menu_page == MENU_NET_IP) {
        render_text((float)fbW/2,(float)(fbH*0.35f),"Gegner-IP eingeben:",0.8f,0.8f,0.9f,1,true);
        int iw = std::min(fbW*2/3, 350), ih = 36;
        int ix = (fbW-iw)/2, iy = fbH/2-ih/2;
        begin_frame();
        fill_rect((float)ix,(float)iy,(float)iw,(float)ih,0.15f,0.13f,0.18f);
        fill_rect((float)ix,(float)iy,(float)iw,2,0.5f,0.4f,0.25f);
        fill_rect((float)ix,(float)(iy+ih-2),(float)iw,2,0.3f,0.25f,0.15f);
        end_frame();
        render_text((float)(ix+8),(float)(iy+ih/2-fs/3),net_ip_buf,0.9f,0.9f,0.9f,1);
        char hint[64]; snprintf(hint,64,"z.B. 192.168.1.100  |  ENTER: verbinden");
        render_text((float)fbW/2,(float)(iy+ih+20),hint,0.4f,0.4f,0.55f,1,true);
    }

    if (menu_page == MENU_RANKING) {
        render_text((float)fbW/2,(float)(fbH*0.08f),"RANGLISTE",0.9f,0.8f,0.55f,1,true);
        int ry = (int)(fbH*0.18f);
        int rh = std::max(22, std::min(fbH/22, 32));
        // Sort by rating descending
        struct { char name[32]; int rating; } sorted[256];
        for(int i=0;i<rating_count;i++){strncpy(sorted[i].name,ratings[i].name,31);sorted[i].rating=ratings[i].rating;}
        for(int i=0;i<rating_count-1;i++)for(int j=i+1;j<rating_count;j++)if(sorted[j].rating>sorted[i].rating){auto t=sorted[i];sorted[i]=sorted[j];sorted[j]=t;}
        int max_show = std::min(rating_count, (int)((fbH*0.6f)/rh));
        for(int i=0;i<max_show;i++){
            char buf[64]; snprintf(buf,64,"%d. %s - %d",i+1,sorted[i].name,sorted[i].rating);
            render_text((float)(fbW/2-120),(float)(ry+i*rh),buf,0.8f,0.8f,0.9f,1);
        }
    }

    if (net_state==NET_CONNECTING||net_state==NET_CONNECTED||net_state==NET_ERROR) {
        render_text((float)fbW/2,(float)(fbH*0.78f),net_info,0.7f,0.7f,0.5f,1,true);
    }
    render_text((float)fbW/2,(float)(fbH-30),"ESC: Zurueck",0.4f,0.4f,0.55f,1,true);
}

// ============================================================
// 3D SYSTEM
// ============================================================
struct vec3 {
    float x,y,z;
    vec3(float x=0,float y=0,float z=0):x(x),y(y),z(z){}
    vec3 operator+(vec3 v)const{return {x+v.x,y+v.y,z+v.z};}
    vec3 operator-(vec3 v)const{return {x-v.x,y-v.y,z-v.z};}
    vec3 operator*(float s)const{return {x*s,y*s,z*s};}
    float dot(vec3 v)const{return x*v.x+y*v.y+z*v.z;}
    vec3 cross(vec3 v)const{return {y*v.z-z*v.y,z*v.x-x*v.z,x*v.y-y*v.x};}
    float len()const{return sqrtf(x*x+y*y+z*z);}
    vec3 norm()const{float l=len();return l>0?*this*(1.0f/l):*this;}
};
struct mat4 {
    float m[16]={0};
    mat4(){}
    static mat4 identity(){mat4 r;r.m[0]=r.m[5]=r.m[10]=r.m[15]=1;return r;}
    static mat4 perspective(float fov,float a,float n,float f){
        mat4 r;float t=1.0f/tanf(fov/2);
        r.m[0]=t/a;r.m[5]=t;r.m[10]=(f+n)/(n-f);r.m[11]=-1;r.m[14]=2*f*n/(n-f);
        return r;
    }
    static mat4 lookAt(vec3 e,vec3 c,vec3 u){
        vec3 f=(c-e).norm(),s=f.cross(u).norm(),t2=s.cross(f);
        mat4 r=identity();
        r.m[0]=s.x;r.m[4]=s.y;r.m[8]=s.z;
        r.m[1]=t2.x;r.m[5]=t2.y;r.m[9]=t2.z;
        r.m[2]=-f.x;r.m[6]=-f.y;r.m[10]=-f.z;
        r.m[12]=-s.dot(e);r.m[13]=-t2.dot(e);r.m[14]=f.dot(e);
        return r;
    }
    static mat4 translate(vec3 v){mat4 r=identity();r.m[12]=v.x;r.m[13]=v.y;r.m[14]=v.z;return r;}
    static mat4 scale(vec3 v){mat4 r=identity();r.m[0]=v.x;r.m[5]=v.y;r.m[10]=v.z;return r;}
    mat4 operator*(mat4 r)const{
        mat4 res;
        for(int i=0;i<4;i++)for(int j=0;j<4;j++)
            res.m[i*4+j]=m[j]*r.m[i*4]+m[4+j]*r.m[i*4+1]+m[8+j]*r.m[i*4+2]+m[12+j]*r.m[i*4+3];
        return res;
    }
};

// Camera
vec3 cam_eye(10,10,10),cam_center(0,0,0);
float cam_dist=12,cam_theta=0.0f,cam_phi=0.7f;
mat4 cam_view,cam_proj;
bool cam_dragging=false;double cam_drag_x,cam_drag_y;
bool enable_3d=true;

void cam_update() {
    cam_eye.x=cam_center.x+cam_dist*sinf(cam_theta)*cosf(cam_phi);
    cam_eye.y=cam_center.y+cam_dist*sinf(cam_phi);
    cam_eye.z=cam_center.z+cam_dist*cosf(cam_theta)*cosf(cam_phi);
    cam_view=mat4::lookAt(cam_eye,cam_center,{0,1,0});
    float ar=(float)fbW/fbH;
    cam_proj=mat4::perspective(0.6f,ar,0.1f,50);
}

// Mesh
struct Mesh3D {GLuint vao=0,vbo=0;int count=0;};
Mesh3D mesh_board,mesh_pieces[7];
bool mesh_ready=false;

void add_vert(std::vector<float>& v,vec3 p,vec3 n,vec3 c) {
    v.insert(v.end(),{p.x,p.y,p.z,n.x,n.y,n.z,c.x,c.y,c.z});
}
vec3 fnormal(vec3 a,vec3 b,vec3 c){return (b-a).cross(c-a).norm();}

void build_mesh(Mesh3D& m,const std::vector<float>& v) {
    if(m.vao)glDeleteVertexArrays(1,&m.vao);
    if(m.vbo)glDeleteBuffers(1,&m.vbo);
    glGenVertexArrays(1,&m.vao);glGenBuffers(1,&m.vbo);
    glBindVertexArray(m.vao);glBindBuffer(GL_ARRAY_BUFFER,m.vbo);
    glBufferData(GL_ARRAY_BUFFER,v.size()*4,v.data(),GL_STATIC_DRAW);
    glVertexAttribPointer(0,3,GL_FLOAT,GL_FALSE,9*4,(void*)0);glEnableVertexAttribArray(0);
    glVertexAttribPointer(1,3,GL_FLOAT,GL_FALSE,9*4,(void*)(3*4));glEnableVertexAttribArray(1);
    glVertexAttribPointer(2,3,GL_FLOAT,GL_FALSE,9*4,(void*)(6*4));glEnableVertexAttribArray(2);
    m.count=(int)v.size()/9;
}

void aq(std::vector<float>& v,vec3 a,vec3 b,vec3 c,vec3 d,vec3 col) {
    vec3 n=fnormal(a,b,c);
    add_vert(v,a,n,col);add_vert(v,b,n,col);add_vert(v,c,n,col);
    add_vert(v,a,n,col);add_vert(v,c,n,col);add_vert(v,d,n,col);
}

void add_cylinder(std::vector<float>& v,int sl,float r,float h,vec3 col,float yb=0) {
    for(int i=0;i<sl;i++){
        float a0=6.283185f*i/sl,a1=6.283185f*(i+1)/sl;
        float c0=cosf(a0),s0=sinf(a0),c1=cosf(a1),s1=sinf(a1);
        vec3 p00(r*c0,yb,r*s0),p01(r*c1,yb,r*s1);
        vec3 p10(r*c0,yb+h,r*s0),p11(r*c1,yb+h,r*s1);
        vec3 n0(c0,0,s0),n1(c1,0,s1);
        add_vert(v,p00,n0,col);add_vert(v,p01,n1,col);add_vert(v,p11,n1,col);
        add_vert(v,p00,n0,col);add_vert(v,p11,n1,col);add_vert(v,p10,n0,col);
        add_vert(v,{0,yb,0},{0,-1,0},col);add_vert(v,p01,{0,-1,0},col);add_vert(v,p00,{0,-1,0},col);
        add_vert(v,{0,yb+h,0},{0,1,0},col);add_vert(v,p10,{0,1,0},col);add_vert(v,p11,{0,1,0},col);
    }
}
void add_sphere_top(std::vector<float>& v,int sl,int st,float r,float y0,float h,vec3 col,float yb=0) {
    float yy0=y0+yb;
    for(int j=0;j<st;j++){
        float t0=(float)j/st*3.14159f/2,t1=(float)(j+1)/st*3.14159f/2;
        float rj0=r*sinf(t0),rj1=r*sinf(t1);
        float yj0=yy0+h*sinf(t0),yj1=yy0+h*sinf(t1);
        for(int i=0;i<sl;i++){
            float a0=6.283185f*i/sl,a1=6.283185f*(i+1)/sl;
            float ca0=cosf(a0),sa0=sinf(a0),ca1=cosf(a1),sa1=sinf(a1);
            vec3 p00(rj0*ca0,yj0,rj0*sa0),p01(rj1*ca0,yj1,rj1*sa0);
            vec3 p10(rj0*ca1,yj0,rj0*sa1),p11(rj1*ca1,yj1,rj1*sa1);
            vec3 n00(sinf(t0)*ca0,cosf(t0),sinf(t0)*sa0);
            vec3 n01(sinf(t1)*ca0,cosf(t1),sinf(t1)*sa0);
            vec3 n10(sinf(t0)*ca1,cosf(t0),sinf(t0)*sa1);
            vec3 n11(sinf(t1)*ca1,cosf(t1),sinf(t1)*sa1);
            add_vert(v,p00,n00,col);add_vert(v,p01,n01,col);add_vert(v,p11,n11,col);
            add_vert(v,p00,n00,col);add_vert(v,p11,n11,col);add_vert(v,p10,n10,col);
        }
    }
}
void add_cone(std::vector<float>& v,int sl,float r,float h,vec3 col,float yb=0) {
    for(int i=0;i<sl;i++){
        float a0=6.283185f*i/sl,a1=6.283185f*(i+1)/sl;
        float c0=cosf(a0),s0=sinf(a0),c1=cosf(a1),s1=sinf(a1);
        vec3 tip(0,yb+h,0),b0(r*c0,yb,r*s0),b1(r*c1,yb,r*s1);
        vec3 sn=fnormal(tip,b1,b0);
        add_vert(v,tip,sn,col);add_vert(v,b1,sn,col);add_vert(v,b0,sn,col);
        add_vert(v,{0,yb,0},{0,-1,0},col);add_vert(v,b1,{0,-1,0},col);add_vert(v,b0,{0,-1,0},col);
    }
}

void gen_piece_mesh(Mesh3D& m,Piece type) {
    std::vector<float> v;int sl=20;
    switch(type){
        case P: // pawn ~0.74
            add_cylinder(v,sl,0.38f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.24f,0.22f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.16f,0.06f,{1,1,1},0.28f);
            add_cylinder(v,sl,0.28f,0.10f,{1,1,1},0.34f);
            add_cylinder(v,sl,0.10f,0.06f,{1,1,1},0.44f);
            add_sphere_top(v,sl,8,0.20f,0,0.24f,{1,1,1},0.50f);
            break;
        case N: // knight ~1.08
            add_cylinder(v,sl,0.38f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.28f,0.20f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.20f,0.08f,{1,1,1},0.26f);
            add_cylinder(v,sl,0.32f,0.14f,{1,1,1},0.34f);
            add_cylinder(v,sl,0.20f,0.18f,{1,1,1},0.48f);
            add_sphere_top(v,sl,8,0.22f,0,0.22f,{1,1,1},0.66f);
            add_cone(v,sl,0.10f,0.20f,{1,1,1},0.88f);
            break;
        case B: // bishop ~1.04
            add_cylinder(v,sl,0.38f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.26f,0.20f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.20f,0.08f,{1,1,1},0.26f);
            add_cylinder(v,sl,0.32f,0.14f,{1,1,1},0.34f);
            add_cone(v,sl,0.32f,0.44f,{1,1,1},0.48f);
            add_sphere_top(v,sl,8,0.12f,0,0.12f,{1,1,1},0.92f);
            break;
        case R: // rook ~0.72
            add_cylinder(v,sl,0.42f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.32f,0.56f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.40f,0.04f,{1,1,1},0.62f);
            add_cylinder(v,sl,0.30f,0.06f,{1,1,1},0.66f);
            break;
        case Q: // queen ~1.16
            add_cylinder(v,sl,0.40f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.30f,0.22f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.22f,0.08f,{1,1,1},0.28f);
            add_cylinder(v,sl,0.34f,0.12f,{1,1,1},0.36f);
            add_sphere_top(v,sl,8,0.32f,0,0.32f,{1,1,1},0.48f);
            add_cylinder(v,sl,0.08f,0.08f,{1,1,1},0.80f);
            add_sphere_top(v,sl,8,0.22f,0,0.18f,{1,1,1},0.88f);
            add_cone(v,sl,0.06f,0.12f,{1,1,1},1.06f);
            break;
        case K: // king ~1.22
            add_cylinder(v,sl,0.40f,0.06f,{1,1,1});
            add_cylinder(v,sl,0.30f,0.22f,{1,1,1},0.06f);
            add_cylinder(v,sl,0.22f,0.08f,{1,1,1},0.28f);
            add_cylinder(v,sl,0.34f,0.14f,{1,1,1},0.36f);
            add_cone(v,sl,0.32f,0.30f,{1,1,1},0.50f);
            add_sphere_top(v,sl,8,0.26f,0,0.22f,{1,1,1},0.80f);
            add_cylinder(v,sl,0.06f,0.25f,{1,1,1},1.02f);
            add_cylinder(v,sl,0.20f,0.04f,{1,1,1},1.14f);
            break;
        default:break;
    }
    build_mesh(m,v);
}

void gen_board() {
    std::vector<float> v;
    float b=4.3f,bh=0.3f;
    vec3 brown(0.22f,0.11f,0.04f),lwood(0.92f,0.82f,0.58f),dwood(0.58f,0.38f,0.14f);
    vec3 silver(0.7f,0.7f,0.78f),milk(0.95f,0.93f,0.87f);
    aq(v,{-b,-bh,-b},{b,-bh,-b},{b,-bh,b},{-b,-bh,b},brown);
    aq(v,{-b,-bh,-b},{b,-bh,-b},{b,0,-b},{-b,0,-b},brown);
    aq(v,{b,-bh,-b},{b,-bh,b},{b,0,b},{b,0,-b},brown);
    aq(v,{b,-bh,b},{-b,-bh,b},{-b,0,b},{b,0,b},brown);
    aq(v,{-b,-bh,b},{-b,-bh,-b},{-b,0,-b},{-b,0,b},brown);
    float ri=0.2f;
    aq(v,{-b,0,-b},{b,0,-b},{b,0,-b+ri},{-b,0,-b+ri},brown);
    aq(v,{b,0,-b},{b,0,b},{b-ri,0,b},{b-ri,0,-b},brown);
    aq(v,{b,0,b},{-b,0,b},{-b,0,b-ri},{b,0,b-ri},brown);
    aq(v,{-b,0,b},{-b,0,-b},{-b+ri,0,-b},{-b+ri,0,b},brown);
    float mw=0.03f;
    aq(v,{-b,0.008f,-b},{b,0.008f,-b},{b,0.008f,-b+mw},{-b,0.008f,-b+mw},milk);
    aq(v,{b,0.008f,-b},{b,0.008f,b},{b-mw,0.008f,b},{b-mw,0.008f,-b},milk);
    aq(v,{b,0.008f,b},{-b,0.008f,b},{-b,0.008f,b-mw},{b,0.008f,b-mw},milk);
    aq(v,{-b,0.008f,b},{-b,0.008f,-b},{-b+mw,0.008f,-b},{-b+mw,0.008f,b},milk);
    float sq=1.0f,sy=0.005f,ri2=ri+0.02f;
    for(int x=0;x<8;x++)for(int y=0;y<8;y++){
        float fx=(float)x-4,fy=(float)y-4;
        vec3 wood=((x+y)%2)?lwood:dwood;
        vec3 side(wood.x*0.6f,wood.y*0.6f,wood.z*0.6f);
        vec3 n0(0,1,0);
        add_vert(v,{fx,sy,fy},n0,wood);add_vert(v,{fx+sq,sy,fy},n0,wood);
        add_vert(v,{fx+sq,sy,fy+sq},n0,wood);
        add_vert(v,{fx,sy,fy},n0,wood);add_vert(v,{fx+sq,sy,fy+sq},n0,wood);
        add_vert(v,{fx,sy,fy+sq},n0,wood);
        float sy1=sy+0.005f;
        aq(v,{fx,sy,fy},{fx+sq,sy,fy},{fx+sq,sy1,fy},{fx,sy1,fy},side);
        aq(v,{fx+sq,sy,fy},{fx+sq,sy,fy+sq},{fx+sq,sy1,fy+sq},{fx+sq,sy1,fy},side);
        aq(v,{fx+sq,sy,fy+sq},{fx,sy,fy+sq},{fx,sy1,fy+sq},{fx+sq,sy1,fy+sq},side);
        aq(v,{fx,sy,fy+sq},{fx,sy,fy},{fx,sy1,fy},{fx,sy1,fy+sq},side);
    }
    float slw=0.012f,sly=0.008f,si=-4+ri2,sf=4-ri2;
    for(int i=1;i<8;i++){
        float p=(float)i-4;
        aq(v,{si,sly,p-slw},{sf,sly,p-slw},{sf,sly,p+slw},{si,sly,p+slw},silver);
        aq(v,{p-slw,sly,si},{p+slw,sly,si},{p+slw,sly,sf},{p-slw,sly,sf},silver);
    }
    build_mesh(mesh_board,v);
}

void init_3d() {
    mesh_ready=false;
    gen_board();
    for(int i=1;i<=6;i++)gen_piece_mesh(mesh_pieces[i],(Piece)i);
    cam_update();
    mesh_ready=true;
}

void render_mesh(const Mesh3D& m,const mat4& model,const mat4& view,const mat4& proj) {
    if(!m.count)return;
    mat4 mvp=proj*view*model;
    glUniformMatrix4fv(glGetUniformLocation(shader_3d,"uMVP"),1,GL_FALSE,mvp.m);
    glUniformMatrix4fv(glGetUniformLocation(shader_3d,"uM"),1,GL_FALSE,model.m);
    glBindVertexArray(m.vao);
    glDrawArrays(GL_TRIANGLES,0,m.count);
}

void render_3d() {
    if(!mesh_ready||!shader_3d)return;
    glViewport(0,0,fbW,fbH);
    glEnable(GL_DEPTH_TEST);
    glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
    glUseProgram(shader_3d);
    glUniform3f(glGetUniformLocation(shader_3d,"uLD"),-0.3f,-0.8f,-0.5f);
    glUniform3f(glGetUniformLocation(shader_3d,"uVP"),cam_eye.x,cam_eye.y,cam_eye.z);
    glUniform1f(glGetUniformLocation(shader_3d,"uAmb"),0.25f);
    glUniform3f(glGetUniformLocation(shader_3d,"uCol"),1,1,1);
    render_mesh(mesh_board,mat4::identity(),cam_view,cam_proj);
    vec3 wc(0.95f,0.92f,0.85f),bc(0.32f,0.16f,0.06f);
    for(int r=0;r<8;r++)for(int f=0;f<8;f++){
        int idx=::sq(f,r);
        if(board.p[idx]==EMPTY)continue;
        vec3 col=board.c[idx]==WHITE?wc:bc;
        glUniform3f(glGetUniformLocation(shader_3d,"uCol"),col.x,col.y,col.z);
        render_mesh(mesh_pieces[board.p[idx]],mat4::translate({(float)f-3.5f,0.005f,(float)r-3.5f}),cam_view,cam_proj);
    }
    glDisable(GL_DEPTH_TEST);
}

int pick_square(double mx,double my) {
    float ndx=(float)(2.0*mx/fbW-1),ndy=(float)(1.0-2.0*my/fbH);
    float aspect=(float)fbW/fbH,fov=0.6f;
    float half_h=tanf(fov/2),half_w=half_h*aspect;
    vec3 ray_ndx(ndx*half_w,ndy*half_h,-1);
    vec3 fwd=(cam_center-cam_eye).norm();
    vec3 side=fwd.cross({0,1,0}).norm();
    vec3 up=side.cross(fwd);
    vec3 world_dir(
        side.x*ray_ndx.x+up.x*ray_ndx.y-fwd.x*ray_ndx.z,
        side.y*ray_ndx.x+up.y*ray_ndx.y-fwd.y*ray_ndx.z,
        side.z*ray_ndx.x+up.z*ray_ndx.y-fwd.z*ray_ndx.z);
    if(fabsf(world_dir.y)<0.0001f)return -1;
    float t=-cam_eye.y/world_dir.y;
    if(t<0)return -1;
    vec3 hit=cam_eye+world_dir*t;
    int fx=(int)(hit.x+4),fy=(int)(hit.z+4);
    if(fx<0||fx>7||fy<0||fy>7)return -1;
    return fy*8+fx;
}



// ============================================================
// MAIN
// ============================================================
int main() {
    if (!glfwInit()) { fprintf(stderr,"glfwInit failed\n"); return -1; }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR,3);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR,3);
    glfwWindowHint(GLFW_OPENGL_PROFILE,GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_DEPTH_BITS,24);

    window = glfwCreateWindow(1024,768,"Schach",nullptr,nullptr);
    if (!window) { glfwTerminate(); return -1; }
    // Initialize Winsock
    WSADATA wsaData;
    if (WSAStartup(MAKEWORD(2,2),&wsaData)!=0) { fprintf(stderr,"WSAStartup failed\n"); return -1; }

    glfwMakeContextCurrent(window);
    glewExperimental = GL_TRUE;
    if (glewInit() != GLEW_OK) { fprintf(stderr,"glewInit failed\n"); return -1; }

    glGenVertexArrays(1,&game_vao);
    glGenBuffers(1,&game_vbo);
    glBindVertexArray(game_vao);
    glBindBuffer(GL_ARRAY_BUFFER,game_vbo);
    glVertexAttribPointer(0,3,GL_FLOAT,GL_FALSE,6*4,(void*)0); glEnableVertexAttribArray(0);
    glVertexAttribPointer(1,3,GL_FLOAT,GL_FALSE,6*4,(void*)(3*4)); glEnableVertexAttribArray(1);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);

    if (!init_shaders()) { fprintf(stderr,"shader init failed\n"); return -1; }
    if (!init_font()) { fprintf(stderr,"font init failed\n"); return -1; }
    init_3d();

    glfwGetFramebufferSize(window, &fbW, &fbH);

    glfwSetMouseButtonCallback(window,on_mouse_button);
    glfwSetKeyCallback(window,on_key);
    glfwSetCharCallback(window,on_char);
    glfwSetCursorPosCallback(window,on_cursor);
    glfwSetScrollCallback(window,[](GLFWwindow*,double,double dy){if(enable_3d){cam_dist*=(float)(1-dy*0.05);if(cam_dist<3)cam_dist=3;if(cam_dist>40)cam_dist=40;cam_update();}});
    glfwSetFramebufferSizeCallback(window,[](GLFWwindow*,int w,int h){fbW=w;fbH=h;need_font_rebake=true;cam_update();});
    glfwSwapInterval(1);

    init_board();
    intro_start = glfwGetTime();

    double last_time = glfwGetTime();

    while (!glfwWindowShouldClose(window)) {
        double now = glfwGetTime();
        float dt = (float)(now-last_time);
        last_time = now;

        audio_update(mode);
        net_poll();

        // State machine
        if (mode == INTRO) {
            if (now - intro_start > 2.0) mode = MENU;
            render_intro();
        } else if (mode == MENU) {
            if (menu_page == MENU_MAIN) render_menu();
            else render_network_menu();
        } else if (mode == OPTIONS) {
            render_options();
        } else if (mode == GAME) {
            // AI move with delay
            if (!net_game && ai_enabled && turn == ai_side && status_msg.find("Schachmatt")==std::string::npos&&status_msg.find("Patt")==std::string::npos) {
                ai_timer += dt;
                if (ai_timer > 0.5) {
                    ai_move(); ai_timer = 0; show_ai_thinking = false;
                    if (status_msg.find("Schachmatt")!=std::string::npos||status_msg.find("Patt")!=std::string::npos) {
                        show_ai_thinking = false;
                    }
                }
            }
            // Network game: rating update on game over
            if (net_game && game_over && net_state==NET_CONNECTED && !net_rating_sent) {
                bool white_wins = status_msg.find("Weiss")!=std::string::npos;
                bool black_wins = status_msg.find("Schwarz")!=std::string::npos;
                if (white_wins||black_wins) {
                    const char* winner = white_wins?net_my_name:net_opp_name;
                    const char* loser = white_wins?net_opp_name:net_my_name;
                    rating_update(winner,loser);
                    ratings_save();
                    net_rating_winner=rating_get(winner); net_rating_loser=rating_get(loser);
                } else {
                    net_rating_winner=rating_get(net_my_name); net_rating_loser=rating_get(net_opp_name);
                }
                char rmsg[64]; snprintf(rmsg,64,"RATING:%d:%d\n",net_rating_winner,net_rating_loser);
                send(net_sock,rmsg,(int)strlen(rmsg),0);
                net_rating_received=true;
                net_rating_sent=true;
            }
            render_game();
        }

        glfwSwapBuffers(window);
        glfwPollEvents();
    }

    net_cleanup();
    WSACleanup();
    if (ttf_data) free(ttf_data);
    glfwTerminate();
    return 0;
}
