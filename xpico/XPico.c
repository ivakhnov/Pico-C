/*-----------------------------------*/
/*            >>>XPico<<<            */
/*            Theo D'Hondt           */
/*          Joeri De Koster          */
/*   VUB Programming Technology Lab  */
/*             (c) 1997              */
/*-----------------------------------*/
/*              Scanning             */
/*-----------------------------------*/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>

#include "Pico.h"
#include "PicoMai.h"
#include "PicoMem.h"
#include "PicoEnv.h"

#define Memory_size 10*1024*1024

#define STDINBUFLEN     10240
#define SPRINTFBUFLEN   10240
#define MSGBUFLEN       10240
#define ACCEPTBUFLEN    10240

#define NAMELEN         512

#define ON_OLD_LINE     0
#define ON_NEW_LINE     1

#define CR             '\x0D'
#define LF             '\x0A'

static char sprintfbuf[SPRINTFBUFLEN];
static char msgbuf[MSGBUFLEN];

static char Memory[Memory_size];

static char last_shown=LF;
static char globalfilename[NAMELEN];
static char *globalfilebuf = NULL;

static char * errors[] = {
   "done",
   "abstract grammar violation",
   "argument type conflict",
   "text buffer overflow",
   "control violation",
   "too many names",
   "digit required",
   "duplicate session identifier",
   "expression violation",
   "excess token(s)",
   "invalid argument",
   "table index violation",
   "invalid index",
   "illegal character",
   "infinite value",
   "invalid parameter",
   "storage overflow",
   "not a boolean",
   "not a function",
   "not a table",
   "number too large",
   "negative argument",
   "non-matching argument list",
   "right brace expected",
   "right bracket expected",
   "reentrancy violation",
   "reference expected",
   "range error",
   "right parenthesis expected",
   "invalid size",
   "session not active",
   "stack error",
   "invalid tag",
   "too many sessions",
   "non-terminated text",
   "undefined identifier",
   "user error",
   "zero division",
   "right colon-bracket expected"
};

static void show(const char s[],
                 const int on_new_line)
  { printf(on_new_line && last_shown != LF ? "\n%s" : "%s", s);
    (void)fflush(stdout);
    while (*s)
      last_shown = *s++; }

static char* read()
  { unsigned index;
    char character;
    for (index = 0;;)
      { scanf("%c", &character);
        if (character == '\n')
          { sprintfbuf[index] = 0;
            return sprintfbuf; }
        sprintfbuf[index++] = character; }}

_ESC_TYPE_ _PICO_PRINT_(const _SES_TYPE_ dummy,
                        const _STR_TYPE_ string)
  { show(string, ON_OLD_LINE);
    return _ESCAPE_NO_; }

_ESC_TYPE_ _PICO_ESCAPE_(const _SES_TYPE_ dummy)
  { return _ESCAPE_NO_; }

_ESC_TYPE_ _PICO_DISPLAY_(const _SES_TYPE_ dummy,
                          const _STR_TYPE_ string)
  { show(string, ON_OLD_LINE);
    return _ESCAPE_NO_; }

_NIL_TYPE_ _PICO_MARK_(const _SES_TYPE_ dummy1,
                       const _POS_TYPE_ start,
                       const _POS_TYPE_ dummy3)
  { _POS_TYPE_ read = 0;
    int line = 1, col = 1;
    char *bufptr = globalfilebuf;
    if (bufptr != NULL)
      { while (read != start)
          { if (*bufptr == LF)
              { line++;
                col = 1; }
            else
              col++;
            read++;
            bufptr++; }
        sprintf(msgbuf,"%s: line %d, col %d", globalfilename, line, col); }}

_NIL_TYPE_ _PICO_MESSAGE_(const _SES_TYPE_ dummy,
                          const _STR_TYPE_ string)
  { strcpy(msgbuf, string); }

_NIL_TYPE_ _PICO_RECLAIM_(const _RCL_TYPE_ r)
  { //return;
    if (r) show("Garbage collect...", ON_NEW_LINE);
    if (!r) show(" done.\n", ON_OLD_LINE); }

static void read_file(char * name)
{
   FILE *file = fopen(name,"r");
   int ch;
   char *bufptr;

   if (file == NULL) {
      sprintf(sprintfbuf, "ERROR: Cannot open file \"%s\": skipping\n", name);
      show(sprintfbuf, ON_NEW_LINE);
      globalfilebuf = NULL;
      return;
   }
   errno = 0;
   (void)fseek(file, 0, SEEK_END);
      /* fseek return value puzzling, using errno */
   if (errno) {
      sprintf(sprintfbuf, "ERROR: Reading file \"%s\": skipping\n", name);
      show(sprintfbuf, ON_NEW_LINE);
      globalfilebuf = NULL;
      return;
   }
   if ((bufptr = globalfilebuf =
            (char *)malloc((size_t)ftell(file)+1)) == NULL) {
      sprintf(sprintfbuf,
             "FATAL ERROR: Cannot allocate %ld bytes to load program text\n",
              ftell(file)+1);
      show(sprintfbuf, ON_NEW_LINE);
      exit(EXIT_FAILURE);
   }
   strncpy(globalfilename, name, NAMELEN);
   globalfilename[NAMELEN-1] = '\0';

   rewind(file);
   while (!feof(file) && ((ch = getc(file)) != EOF))
      *bufptr++ = (char)ch;
   *bufptr = '\0';

   (void)fclose(file);
}

static void error_loop(int err)
  { char acceptbuf[ACCEPTBUFLEN];
    char *bufptr;
    while (err < _PICO_DONE_)
      switch (err) {
        case _DO_ESCAPE_:
          show("User Break\n", ON_NEW_LINE);
          return;
        case _DO_ACCEPT_:
          *acceptbuf = '\0'; /* avoid dirty crash when input = ctrl-d */
          bufptr = fgets(acceptbuf, ACCEPTBUFLEN, stdin);
          bufptr = acceptbuf; /* same reason as above */
          while ((*bufptr != LF) && (*bufptr != CR) && *bufptr)
            bufptr++;
          *bufptr = '\0';
          last_shown = LF;
          err = _PICO_ACCEPT_(1, acceptbuf);
          break;
        case _DO_LOAD_:
          if (read_file(msgbuf), globalfilebuf != NULL)
            { msgbuf[0] = '\0';
              err = _PICO_LOAD_(1, globalfilebuf);
              free(globalfilebuf);
              globalfilebuf = NULL; }
          else
            { msgbuf[0] = '\0';
              err = _PICO_LOAD_(1, "display(\"\")"); }
          break; }

   switch (err) {
      case _PICO_DONE_:
         break;
      case _CTL_ERROR_:
      case _DCT_ERROR_:
      case _MEM_ERROR_:
      case _REE_ERROR_:
      case _STK_ERROR_:
         sprintf(sprintfbuf, "FATAL ERROR: %s\n", errors[err]);
         show(sprintfbuf, ON_NEW_LINE);
         exit(EXIT_FAILURE);
      default:
         sprintf(sprintfbuf, "ERROR: %s", errors[err]);
         show(sprintfbuf, ON_NEW_LINE);
         if (msgbuf[0]) {
            sprintf(sprintfbuf, " (%s)\n", msgbuf);
            show(sprintfbuf, ON_OLD_LINE);
         }
         else show("\n", ON_OLD_LINE);
   }
}

int main (int argc, const char * argv[])
  { char *line = NULL;
    _PICO_INIT_(Memory, Memory_size);
    assert(!_PICO_SESSION_(1));
    while (!feof(stdin))
      { show(">", ON_NEW_LINE);
        line = read();
        last_shown = LF;
        if (!line[0] || line[0] == CR || line[0] == LF)
          { continue; }
         msgbuf[0] = '\0';
         error_loop(_PICO_DO_(1, line)); }
    return 0; }
