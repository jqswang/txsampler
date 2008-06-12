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

#ifndef prof_juicy_Prof_CallPath_Profile_hpp 
#define prof_juicy_Prof_CallPath_Profile_hpp

//************************* System Include Files ****************************

#include <iostream>
#include <vector>

//*************************** User Include Files ****************************

#include <include/general.h>

#include "MetricDesc.hpp"
#include "Epoch.hpp"
#include "CCT-Tree.hpp"

//*************************** Forward Declarations ***************************

//***************************************************************************
// Profile
//***************************************************************************

namespace Prof {

namespace CallPath {

class Profile: public Unique {
public:
  Profile(uint numMetrics);
  virtual ~Profile();
  
  // -------------------------------------------------------
  // Data
  // -------------------------------------------------------
  const std::string& name() const 
    { return m_name; }
  void name(const char* s) 
    { m_name = (s) ? s : ""; }

  uint numMetrics() const
    { return m_metricdesc.size(); }
  SampledMetricDesc* metric(uint i) const 
    { return m_metricdesc[i]; }
  const SampledMetricDescVec& metricDesc() const 
    { return m_metricdesc; }

  CCT::Tree*  cct() const 
    { return m_cct; }

  Epoch* epoch() const
    { return m_epoch; }
  void epoch(Epoch* x) 
    { m_epoch = x; }

  // -------------------------------------------------------
  // 
  // -------------------------------------------------------

  // Given a Profile y, merge y into x = 'this'
  // ASSUMES: both x and y are in canonical form (cct_canonicalize())
  // WARNING: the merge may change/destroy y
  void merge(Profile& y);

  // -------------------------------------------------------
  // 
  // -------------------------------------------------------
  static Profile* make(const char* fnm);

  // -------------------------------------------------------
  // Dump contents for inspection
  // -------------------------------------------------------
  virtual void dump(std::ostream& os = std::cerr) const;
  virtual void ddump() const;

private:

  // 1. annotate CCT::Tree nodes with associated Prof::Epoch::LM_id_t 
  // 2. normalize CCT::Tree node IPs (unrelocate)
  void 
  cct_canonicalize();

  void 
  cct_applyEpochMergeChanges(std::vector<Epoch::MergeChange>& mergeChg);
 
private:
  std::string m_name;

  CCT::Tree* m_cct;
  SampledMetricDescVec m_metricdesc;
  Epoch* m_epoch;
};

} // namespace CallPath

} // namespace Prof


//***************************************************************************


//***************************************************************************

#endif /* prof_juicy_Prof_CallPath_Profile_hpp */
