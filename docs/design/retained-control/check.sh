#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
proof_build_dir=$(mktemp -d)
trap 'rm -rf -- "$proof_build_dir"' EXIT
export LEAN_PATH="$proof_build_dir"
# Reviewed proof registrations follow.
lean -DwarningAsError=true -o "$proof_build_dir/Ownership.olean" Ownership.lean
lean -DwarningAsError=true -o "$proof_build_dir/OwnershipExamples.olean" OwnershipExamples.lean
lean -DwarningAsError=true -o "$proof_build_dir/DrainSafety.olean" DrainSafety.lean
lean -DwarningAsError=true -o "$proof_build_dir/WorkerChannel.olean" WorkerChannel.lean
lean -DwarningAsError=true -o "$proof_build_dir/OneWayCompletion.olean" OneWayCompletion.lean

# N3 ledger models and their recorded axiom reports.
for module in \
  NetworkLedgerAllocation NetworkLedgerCollections NetworkLedgerChecker \
  NetworkLedgerCoreRemoval NetworkLedgerCoreStrict NetworkLedgerCoreRegion \
  NetworkLedgerCoreEval NetworkLedgerCoreValues NetworkLedgerCoreLookup \
  NetworkLedgerCoreRecordProjection NetworkLedgerCoreRecordLookup NetworkLedgerCoreRecordRemoval \
  NetworkLedgerCoreInsert NetworkLedgerCoreGenericInsert NetworkLedgerCoreIncrement \
  NetworkLedgerCoreInitialization NetworkLedgerCoreInsertBinding NetworkLedgerCoreRecordUpdate \
  NetworkLedgerTransitions NetworkLedgerRegistrationCheck NetworkLedgerCoreRecordRegistration \
  NetworkLedgerCoreRootInitialization NetworkLedgerClosureCheck NetworkLedgerRetirementCheck \
  NetworkLedgerAcknowledgementCheck NetworkLedgerReachability NetworkLedgerCoupling \
  NetworkLedgerMessage NetworkLedgerTokens NetworkLedgerProtocol NetworkLedgerNetwork \
  NetworkLedgerHistoryControl NetworkLedgerCoverageClosure
do
  lean -DwarningAsError=true -o "$proof_build_dir/$module.olean" "$module.lean"
done
lean -DwarningAsError=true NetworkLedgerAxioms.lean
lean -DwarningAsError=true NetworkLedgerClosureAxioms.lean
