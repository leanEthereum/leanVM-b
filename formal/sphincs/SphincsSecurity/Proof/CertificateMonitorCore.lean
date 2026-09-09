import SphincsSecurity.Proof.CertificateBankCompleteness

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

structure CertificateCore where
  log : QueryLog SigningSpec
  spent : Nat
  messageCalls : Nat
  proposals : Nat
  creationMass : ENNReal
  stopped : Bool

structure CertificateLedger where
  creationCost : ENNReal
  bank : HashInput → Bool

def certificateCore (monitor : CertificateMonitor) : CertificateCore :=
  ⟨monitor.log, monitor.spent, monitor.messageCalls, monitor.proposals, monitor.creationMass, monitor.stopped⟩

def certificateLedger (monitor : CertificateMonitor) : CertificateLedger :=
  ⟨monitor.creationCost, monitor.bank⟩

def CertificateCore.attach (core : CertificateCore) (ledger : CertificateLedger) : CertificateMonitor :=
  ⟨core.log, core.spent, core.messageCalls, core.proposals, core.creationMass,
    ledger.creationCost, ledger.bank, core.stopped⟩

theorem certificateCore_attach (core : CertificateCore) (ledger : CertificateLedger) :
    certificateCore (core.attach ledger) = core := rfl

theorem certificateCore_attach_ledger (monitor : CertificateMonitor) :
    (certificateCore monitor).attach (certificateLedger monitor) = monitor := rfl

abbrev CertificateCoreStopRule := (input : (OracleWorld + SigningSpec).Domain) →
  (QueryCache HashSpec × CertificateCore) → Nat → ProposalExecutionRecord input → Bool

def certificateCoreStop (stopAfter : CertificateCoreStopRule) : CertificateStopRule :=
  fun input state length record => stopAfter input (state.1, certificateCore state.2) length record

noncomputable def certificateCoreGuard (stopAfter : CertificateCoreStopRule) : CertificateCoreStopRule :=
  fun input state length record => proposalPrefixStop input (state.1, state.2.attach ⟨0, fun _ => false⟩)
    length record || stopAfter input state length record

theorem certificateCoreStop_guard (stopAfter : CertificateCoreStopRule) :
    certificateCoreStop (certificateCoreGuard stopAfter) =
      fun input state length record => proposalPrefixStop input state length record ||
        certificateCoreStop stopAfter input state length record := rfl

theorem certificateMonitorEnabled_attach (key : SecretKey) (budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (core : CertificateCore)
    (left right : CertificateLedger) :
    certificateMonitorEnabled key budget message (cache, core.attach left) =
      certificateMonitorEnabled key budget message (cache, core.attach right) := rfl

theorem certificateMonitorUpdate_core (key : SecretKey) (budget : Nat)
    (leftRequired rightRequired : Finset FtsTree) (stopAfter : CertificateCoreStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (core : CertificateCore) (left right : CertificateLedger) (length : Nat)
    (record : ProposalExecutionRecord input) :
    certificateCore (certificateMonitorUpdate key budget leftRequired (certificateCoreStop stopAfter)
      input (cache, core.attach left) length record) =
    certificateCore (certificateMonitorUpdate key budget rightRequired (certificateCoreStop stopAfter)
      input (cache, core.attach right) length record) := by
  simp only [certificateMonitorUpdate, CertificateMonitorActive, CertificateMonitorReady,
    CertificateCore.attach, certificateCoreStop, certificateCore, proposalRecordLogState]
  split <;> rfl

def certificateRequiredTrees : Option FtsTree → Finset FtsTree
  | none => Finset.univ
  | some omitted => Finset.univ.erase omitted

structure CertificateFamilyMonitor where
  core : CertificateCore
  ledger : Option FtsTree → CertificateLedger
  cacheHit : Bool

abbrev CertificateFamilyState := QueryCache HashSpec × CertificateFamilyMonitor

def certificateFamilyProject (index : Option FtsTree) (state : CertificateFamilyState) :
    CertificateCacheMonitorState :=
  (state.1, state.2.core.attach (state.2.ledger index), state.2.cacheHit)

noncomputable def certificateFamilyUpdate (key : SecretKey) (budget : Nat)
    (stopAfter : CertificateCoreStopRule) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateFamilyState) (length : Nat) (record : ProposalExecutionRecord input) : CertificateFamilyMonitor :=
  let update := fun index => certificateCacheMonitorUpdate key budget (certificateRequiredTrees index)
    (certificateCoreStop stopAfter) input (certificateFamilyProject index state) length record
  ⟨certificateCore (update none).1, fun index => certificateLedger (update index).1, (update none).2⟩

theorem certificateFamilyUpdate_project (key : SecretKey) (budget : Nat)
    (stopAfter : CertificateCoreStopRule) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateFamilyState) (length : Nat) (record : ProposalExecutionRecord input)
    (index : Option FtsTree) :
    certificateFamilyProject index (record.cache, certificateFamilyUpdate key budget stopAfter input state length record) =
      (record.cache, certificateCacheMonitorUpdate key budget (certificateRequiredTrees index)
        (certificateCoreStop stopAfter) input (certificateFamilyProject index state) length record) := by
  simp only [certificateFamilyUpdate, certificateFamilyProject, certificateCacheMonitorUpdate,
    certificateCacheMonitorProject]
  rw [certificateMonitorUpdate_core key budget (certificateRequiredTrees none) (certificateRequiredTrees index)
    stopAfter input state.1 state.2.core (state.2.ledger none) (state.2.ledger index) length record,
    certificateCore_attach_ledger]

def initialCertificateFamilyMonitor (spent : Nat) (stopped : Bool) : CertificateFamilyMonitor :=
  ⟨certificateCore (initialCertificateMonitor spent stopped),
    fun _ => certificateLedger (initialCertificateMonitor spent stopped), false⟩

theorem certificateFamilyProject_initial (index : Option FtsTree) (spent : Nat) (stopped : Bool)
    (cache : QueryCache HashSpec) :
    certificateFamilyProject index (cache, initialCertificateFamilyMonitor spent stopped) =
      (cache, initialCertificateMonitor spent stopped, false) := rfl

end SphincsSecurity.Concrete
