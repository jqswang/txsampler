// -*-Mode: C++;-*-
// $Id$

// * BeginRiceCopyright *****************************************************
// 
// Copyright ((c)) 2002-2007, Rice University 
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
// 
// * Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.
// 
// * Neither the name of Rice University (RICE) nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
// 
// This software is provided by RICE and contributors "as is" and any
// express or implied warranties, including, but not limited to, the
// implied warranties of merchantability and fitness for a particular
// purpose are disclaimed. In no event shall RICE or contributors be
// liable for any direct, indirect, incidental, special, exemplary, or
// consequential damages (including, but not limited to, procurement of
// substitute goods or services; loss of use, data, or profits; or
// business interruption) however caused and on any theory of liability,
// whether in contract, strict liability, or tort (including negligence
// or otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage. 
// 
// ******************************************************* EndRiceCopyright *

//***************************************************************************
//
// File:
//   $Source$
//
// Purpose:
//   [The purpose of this file]
//
// Description:
//   [The set of functions, macros, etc. defined in the file]
//
//***************************************************************************

//************************* System Include Files ****************************

#include <iostream>
using std::cerr;
using std::endl;

#include <string>
using std::string;

//*************************** User Include Files ****************************

#include "Args.hpp"

#include <lib/support/diagnostics.h>
#include <lib/support/Trace.hpp>
#include <lib/support/StrUtil.hpp>

//*************************** Forward Declarations **************************

#define ARG_Throw(streamArgs) DIAG_ThrowX(Args::Exception, streamArgs)

// Cf. DIAG_Die.
#define ARG_ERROR(streamArgs)                                        \
  { std::ostringstream WeIrDnAmE;                                    \
    WeIrDnAmE << streamArgs /*<< std::ends*/;                        \
    printError(std::cerr, WeIrDnAmE.str());                          \
    exit(1); }

//***************************************************************************

static const char* version_info =
#include <include/HPCToolkitVersionInfo.h>

static const char* usage_summary1 =
"[--source] [options] <profile-file>...";

static const char* usage_summary2 =
"--object [options] <profile-file>...";

static const char* usage_summary3 =
"--dump <profile-file>...\n";

static const char* usage_details = "\
hpcproftt correlates 'flat' profile metrics with either source code structure\n\
(the first and default mode) or object code (second mode) and generates\n\
textual output suitable for a terminal.  In both of these modes, hpcproftt\n\
expects a list of flat profile files. hpcproftt also supports a third mode\n\
in which it generates textual dumps of profile files.  In this mode, the\n\
profile list may contain either flat or call path profile files.\n\
\n\
hpcproftt defaults to source code correlation mode. Without any mode switch,\n\
it behaves as if passed --source=pgm,lm.\n\
\n\
Options: General:\n\
  -v [<n>], --verbose [<n>]\n\
                       Verbose: generate progress messages to stderr at\n\
                       verbosity level <n>. {1}\n\
  -V, --version        Print version information.\n\
  -h, --help           Print this help.\n\
  --debug [<n>]        Debug: use debug level <n>. {1}\n\
\n\
Options: Source Structure Correlation:\n\
  --source[=all,sum,pgm,lm,f,p,l,s,src]\n\
  --src[=all,sum,pgm,lm,f,p,l,s,src]\n\
                       Correlate metrics to source code structure. Without\n\
                       --source, default is {pgm,lm}; with, it is {sum}\n\
                         all: all summaries plus annotated source files\n\
                         sum: all summaries\n\
                         pgm: program summary\n\
                         lm:  load module summary\n\
                         f:   file summary\n\
                         p:   procedure summary\n\
                         l:   loop summary\n\
                         s:   statement summary\n\
                         src: annotate source files; equiv to --srcannot '*'\n\
  --srcannot <glob>    Annotate source files with path names that match\n\
                       file glob <glob>. Protect globs from the shell with\n\
                       'single quotes'. May pass multiple times.\n\
  -M <metric>, --metric <metric>\n\
                       Show a supplemental or different metric set. <metric>\n\
                       is one of the following:\n\
                         sum:      Additionally show Mean, RStdDev, Min, Max\n\
                         sum-only: Show only Mean, RStdDev, Min, Max\n\
\n\
  -I <path>, --include <path>\n\
                       Use <path> when searching for source files. For a\n\
                       recursive search, append a '*' after the last slash,\n\
                       e.g., '/mypath/*'. (Quote or escape to protect from\n\
                       shell.) May pass multiple times.\n\
  -S <file>, --structure <file>\n\
                       Use hpcstruct structure file <file> for correlation.\n\
                       May pass multiple times (e.g., for shared libraries).\n\
\n\
Options: Object Correlation:\n\
  --object[=s]         Correlate metrics with object code by annotating\n\
  --obj[=s]            object code procedures and instructions. {}\n\
                         s: intermingle source line info with object code\n\
  --obj-values         Show raw metrics as values instead of percents\n\
  --obj-threshold <n>  Prune procedures with an event count < n {1}\n\
\n\
Options: Dump Raw Profile Data:\n\
  --dump               Generate textual representation of raw profile data.\n\
";


static bool isOptArg_src(const char* x);
static bool isOptArg_obj(const char* x);


#define CLP CmdLineParser
#define CLP_SEPARATOR "!!!"

// Note: Changing the option name requires changing the name in Parse()
CmdLineParser::OptArgDesc Args::optArgs[] = {
  // Source structure correlation options
  {  0 , "source",          CLP::ARG_OPT,  CLP::DUPOPT_CLOB, NULL,
     isOptArg_src },
  {  0 , "src",             CLP::ARG_OPT,  CLP::DUPOPT_CLOB, NULL,
     isOptArg_src },
  {  0 , "srcannot",        CLP::ARG_REQ,  CLP::DUPOPT_CAT,  CLP_SEPARATOR,
     NULL },
  { 'I', "include",         CLP::ARG_REQ,  CLP::DUPOPT_CAT,  CLP_SEPARATOR,
     NULL },
  { 'S', "structure",       CLP::ARG_REQ,  CLP::DUPOPT_CAT,  CLP_SEPARATOR,
     NULL },
  { 'M', "metric",          CLP::ARG_REQ,  CLP::DUPOPT_CLOB, NULL,
     NULL },

  // Object correlation options
  {  0 , "object",          CLP::ARG_OPT , CLP::DUPOPT_CLOB, NULL,
     isOptArg_obj },
  {  0 , "obj",             CLP::ARG_OPT , CLP::DUPOPT_CLOB, NULL,
     isOptArg_obj },
  {  0 , "obj-values",      CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL,
     NULL },
  {  0 , "obj-threshold",   CLP::ARG_REQ,  CLP::DUPOPT_CLOB, NULL,
     NULL },

  // OBSOLETE Options
  { 'e', NULL, CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL, NULL}, // everything
  { 'f', NULL, CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL, NULL}, // files
  { 'r', NULL, CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL, NULL}, // routines
  { 'l', NULL, CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL, NULL}, // lines
  { 'o', NULL, CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL, NULL}, // object

  // Raw profile data
  {  0 , "dump",            CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL,
     NULL },

  // General
  { 'v', "verbose",         CLP::ARG_OPT,  CLP::DUPOPT_CLOB, NULL,
     NULL },
  { 'V', "version",         CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL,
     NULL },
  { 'h', "help",            CLP::ARG_NONE, CLP::DUPOPT_CLOB, NULL,
     NULL },
  {  0 , "debug",           CLP::ARG_OPT,  CLP::DUPOPT_CLOB, NULL,  // hidden
     NULL },
  CmdLineParser_OptArgDesc_NULL_MACRO // SGI's compiler requires this version
};

#undef CLP


static bool 
isOptArg_src(const char* x)
{
  string opt(x);
  bool ret = true;
  try {
    Args::parse_sourceOpts(NULL, opt);
  }
  catch (const Args::Exception& x) {
    // To enable good error messages, consider strings with a ratio of
    // commas:characters >= 1/3 to be an attempt at a src argument.
    // NOTE: this metric assumes an implicit comma at the end of the string
    const double tolerance = 1.0/3.0;

    double commas = 1;
    for (size_t p = 0; (p = opt.find_first_of(',', p)) != string::npos; ++p) {
      commas += 1;
    }

    double characters = opt.size();
    
    ret = (commas / characters) >= tolerance;
  }
  return ret;
}


static bool 
isOptArg_obj(const char* x)
{
  string opt(x);
  bool ret = true;
  try {
    Args::parse_objectOpts(NULL, opt);
  }
  catch (const Args::Exception& x) {
    // To enable good error messages, consider strings of size 1
    return (opt.size() == 1);
  }
  return ret;
}


//***************************************************************************
// Args
//***************************************************************************

Args::Args()
{
  Ctor();
}


Args::Args(int argc, const char* const argv[])
{
  Ctor();
  parse(argc, argv);
}


void
Args::Ctor()
{
  mode = Mode_SourceCorrelation;

  obj_metricsAsPercents = true;
  obj_showSourceCode = false;
  obj_procThreshold = 1;

  Diagnostics_SetDiagnosticFilterLevel(1);


  // override Analysis::Args defaults
  out_db_experiment = "";
  db_dir            = "";
  db_copySrcFiles   = false;

  out_txt           = "-";
  txt_summary       = TxtSum_fPgm | TxtSum_fLM;
  txt_srcAnnotation = false;
  metrics_computeInteriorValues = true; // dump metrics on interior nodes
}


Args::~Args()
{
}


void 
Args::printVersion(std::ostream& os) const
{
  os << getCmd() << ": " << version_info << endl;
}


void 
Args::printUsage(std::ostream& os) const
{
  os << "Usage: \n"
     << "  " << getCmd() << " " << usage_summary1 << endl
     << "  " << getCmd() << " " << usage_summary2 << endl
     << "  " << getCmd() << " " << usage_summary3 << endl
     << usage_details << endl;
} 


void 
Args::printError(std::ostream& os, const char* msg) /*const*/
{
  os << getCmd() << ": " << msg << endl
     << "Try `" << getCmd() << " --help' for more information." << endl;
}

void 
Args::printError(std::ostream& os, const std::string& msg) /*const*/
{
  printError(os, msg.c_str());
}


const std::string& 
Args::getCmd() /*const*/
{ 
  // avoid error messages with: .../bin/hpcproftt-bin
  static string cmd = "hpcproftt";
  return cmd; // parser.getCmd(); 
}


void
Args::parse(int argc, const char* const argv[])
{
  try {
    // -------------------------------------------------------
    // Parse the command line
    // -------------------------------------------------------
    parser.parse(optArgs, argc, argv);
    
    // -------------------------------------------------------
    // Sift through results, checking for semantic errors
    // -------------------------------------------------------
    
    // Special options that should be checked first
    if (parser.isOpt("debug")) {
      int dbg = 1;
      if (parser.isOptArg("debug")) {
	const string& arg = parser.getOptArg("debug");
	dbg = (int)CmdLineParser::toLong(arg);
      }
      Diagnostics_SetDiagnosticFilterLevel(dbg);
      trace = dbg;
    }
    if (parser.isOpt("help")) { 
      printUsage(std::cerr); 
      exit(1);
    }
    if (parser.isOpt("version")) { 
      printVersion(std::cerr);
      exit(1);
    }
    if (parser.isOpt("verbose")) {
      int verb = 1;
      if (parser.isOptArg("verbose")) {
	const string& arg = parser.getOptArg("verbose");
	verb = (int)CmdLineParser::toLong(arg);
      }
      Diagnostics_SetDiagnosticFilterLevel(verb);
    }

    // Check for other options: Source correlation options
    if (parser.isOpt("source") || parser.isOpt("src")) {
      mode = Mode_SourceCorrelation;
      txt_summary = TxtSum_ALL;
      
      string opt;
      if (parser.isOptArg("source"))   { opt = parser.getOptArg("source"); }
      else if (parser.isOptArg("src")) { opt = parser.getOptArg("src"); }

      if (!opt.empty()) {
	txt_summary = Analysis::Args::TxtSum_NULL;
	parse_sourceOpts(this, opt);
      }
    }
    if (parser.isOpt("srcannot")) {
      txt_srcAnnotation = true;
      string str = parser.getOptArg("srcannot");
      StrUtil::tokenize_str(str, CLP_SEPARATOR, txt_srcFileGlobs);
    }
    if (parser.isOpt("include")) {
      string str = parser.getOptArg("include");
      StrUtil::tokenize_str(str, CLP_SEPARATOR, searchPaths);
      
      for (uint i = 0; i < searchPaths.size(); ++i) {
	searchPathTpls.push_back(Analysis::PathTuple(searchPaths[i], "src"));
      }
    }
    if (parser.isOpt("structure")) {
      string str = parser.getOptArg("structure");
      StrUtil::tokenize_str(str, CLP_SEPARATOR, structureFiles);
    }
    if (parser.isOpt("metric")) {
      string opt = parser.getOptArg("metric");
      parse_metricOpts(this, opt);
    }
    
    // Check for other options: Object correlation options
    if (parser.isOpt("object") || parser.isOpt("obj")) {
      mode = Mode_ObjectCorrelation;

      string opt;
      if (parser.isOptArg("object"))   { opt = parser.getOptArg("object"); }
      else if (parser.isOptArg("obj")) { opt = parser.getOptArg("obj"); }

      if (!opt.empty()) {
	parse_objectOpts(this, opt);
      }
    }
    if (parser.isOpt("obj-values")) {
      obj_metricsAsPercents = false;
    }
    if (parser.isOpt("obj-threshold")) {
      const string& arg = parser.getOptArg("obj-threshold");
      obj_procThreshold = CmdLineParser::toUInt64(arg);
    }

    // Check for other options: Dump raw profile data
    if (parser.isOpt("dump")) {
      mode = Mode_RawDataDump;
    }

    // -------------------------------------------------------
    // OBSOLETE Options [FIXME: remove as soon as SiCortex says ok]
    // -------------------------------------------------------
    if (parser.isOpt('e')) {
      DIAG_WMsg(0, "Deprecated option '-e': use --src=all or --src=sum");
      mode = Mode_SourceCorrelation;
      txt_summary = TxtSum_ALL;
      txt_srcAnnotation = true;
    }
    if (parser.isOpt('f')) {
      DIAG_WMsg(0, "Deprecated option '-f': use --src=f");
      mode = Mode_SourceCorrelation;
      txt_summary = txt_summary | TxtSum_fFile;
    }
    if (parser.isOpt('r')) {
      DIAG_WMsg(0, "Deprecated option '-r': use --src=p");
      mode = Mode_SourceCorrelation;
      txt_summary = txt_summary | TxtSum_fProc;
    }
    if (parser.isOpt('l')) {
      DIAG_WMsg(0, "Deprecated option '-l': use --src=s");
      mode = Mode_SourceCorrelation;
      txt_summary = txt_summary | TxtSum_fStmt;
    }
    if (parser.isOpt('o')) {
      DIAG_WMsg(0, "Deprecated option '-o': use --obj");
      mode = Mode_ObjectCorrelation;
    }

    // FIXME: sanity check that options correspond to mode
    
    // Check for required arguments
    uint numArgs = parser.getNumArgs();
    if ( !(numArgs >= 1) ) {
      ARG_ERROR("Incorrect number of arguments!");
    }

    profileFiles.resize(numArgs);
    for (uint i = 0; i < numArgs; ++i) {
      profileFiles[i] = parser.getArg(i);
    }
  }
  catch (const CmdLineParser::ParseError& x) {
    ARG_ERROR(x.what());
  }
  catch (const CmdLineParser::Exception& x) {
    DIAG_EMsg(x.message());
    exit(1);
  }
  catch (const Args::Exception& x) {
    ARG_ERROR(x.what());
  }
}


void
Args::parse_sourceOpts(Args* args, const string& opts)
{
  std::vector<std::string> srcOptVec;
  StrUtil::tokenize_char(opts, ",", srcOptVec);

  for (uint i = 0; i < srcOptVec.size(); ++i) {
    const string& opt = srcOptVec[i];
    
    Analysis::Args::TxtSum flg = Analysis::Args::TxtSum_NULL;
    if      (opt == "all") { flg = TxtSum_ALL; }
    else if (opt == "sum") { flg = TxtSum_ALL; }
    else if (opt == "pgm") { flg = TxtSum_fPgm; }
    else if (opt == "lm")  { flg = TxtSum_fLM; }
    else if (opt == "f")   { flg = TxtSum_fFile; }
    else if (opt == "p")   { flg = TxtSum_fProc; }
    else if (opt == "l")   { flg = TxtSum_fLoop; }
    else if (opt == "s")   { flg = TxtSum_fStmt; }
    else if (opt == "src") { ; }
    else {
      ARG_Throw("Unknown argument to --src,--source: '" << opt << "'");
    }

    if (args) {
      args->txt_summary = (args->txt_summary | flg);
      if (opt == "all" || opt == "src") {
	args->txt_srcAnnotation = true;
      }
    }
  }
}


void
Args::parse_objectOpts(Args* args, const string& opts)
{
  if (opts == "s") {
    if (args) {
      args->obj_showSourceCode = true;
    }
  }
  else {
    ARG_Throw("Unknown argument to --obj,--object: '" << opts << "'");
  }
}


void
Args::parse_metricOpts(Args* args, const string& opts)
{
  if (opts == "sum" || opts == "sum-only") {
    if (args) {
      args->txt_metrics = opts;
    }
  }
  else {
    ARG_Throw("Unknown argument to -M,--metric: '" << opts << "'");
  }
}


void 
Args::dump(std::ostream& os) const
{
  os << "Args.cmd= " << getCmd() << endl; 
  Analysis::Args::dump(os);
}

