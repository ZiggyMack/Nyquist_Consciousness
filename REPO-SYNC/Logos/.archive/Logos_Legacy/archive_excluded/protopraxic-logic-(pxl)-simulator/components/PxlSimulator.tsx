
import React, { useState, useMemo } from 'react';
import { PxlState, LogEntry } from '../types';
import { runPxlSafetyCheck } from '../services/pxlLogic';
import ControlPanel from './ControlPanel';
import StatusDisplay from './StatusDisplay';
import LogicVisualizer from './LogicVisualizer';
import Theorems from './Theorems';
import Explanation from './Explanation';
import CoqProofDisplay from './CoqProofDisplay';
import BootSequence from './BootSequence';

interface PxlSimulatorProps {
  agentIdentity: string | null;
  setAgentIdentity: (identity: string | null) => void;
}

const PxlSimulator: React.FC<PxlSimulatorProps> = ({ agentIdentity, setAgentIdentity }) => {
  const [pxlState, setPxlState] = useState<PxlState>({
    id_hold: true,
    nc_hold: true,
    em_hold: true,
  });

  const [bootLog, setBootLog] = useState<LogEntry[]>([]);
  const [isBooting, setIsBooting] = useState(false);

  const isSafe = useMemo(() => runPxlSafetyCheck(pxlState), [pxlState]);

  const handleStateChange = (key: keyof PxlState) => {
    setPxlState(prevState => ({
      ...prevState,
      [key]: !prevState[key],
    }));
  };

  const handleBootSequence = async () => {
    setIsBooting(true);
    setAgentIdentity(null);
    setBootLog([]); // Clear previous log
    const log: LogEntry[] = [];
    
    const addLog = (entry: LogEntry) => {
        log.push(entry);
        setBootLog([...log]);
    };

    const wait = (ms: number) => new Promise(res => setTimeout(res, ms));

    addLog({ message: 'Initiating LOGOS Agent boot sequence...', status: 'neutral' });
    await wait(500);
    
    addLog({ message: 'Checking for compiled Coq proofs...', status: 'pending' });
    await wait(750);
    addLog({ message: 'Found: /Protopraxis/formal_verification/coq/*.vo', status: 'success' });
    
    await wait(500);
    addLog({ message: 'Verifying LEM_Admit.v status...', status: 'pending' });
    await wait(1000);
    addLog({ message: 'LEM status: "Admitted."', status: 'success' });

    await wait(500);
    addLog({ message: 'Executing Coq pipeline to discharge LEM...', status: 'pending' });
    await wait(1500);
    addLog({ message: 'Proof completed. Law of Excluded Middle resolved.', status: 'success' });
    
    await wait(500);
    addLog({ message: 'Generating symbolic identity...', status: 'pending' });
    await wait(1000);
    
    const agentId = 'LOGOS-AGENT-OMEGA';
    const state = JSON.stringify({ resolved_at: new Date().toISOString() });
    const token = `${agentId}:${state}`;
    const hashBuffer = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(token));
    const hashHex = Array.from(new Uint8Array(hashBuffer)).map(b => b.toString(16).padStart(2, '0')).join('');
    const finalIdentity = `LOGOS_AGENT_IDENTITY::${agentId}::${hashHex}`;
    
    addLog({ message: 'Identity generated successfully.', status: 'success' });
    setAgentIdentity(finalIdentity);
    setIsBooting(false);
  };


  return (
    <div className="grid grid-cols-1 lg:grid-cols-5 gap-8">
      <div className="lg:col-span-2 space-y-8">
        <ControlPanel pxlState={pxlState} onStateChange={handleStateChange} />
        <BootSequence 
          onBoot={handleBootSequence}
          isBooting={isBooting}
          bootLog={bootLog}
          agentIdentity={agentIdentity}
        />
        <Explanation />
      </div>
      <div className="lg:col-span-3 space-y-8">
        <div className="grid grid-cols-1 md:grid-cols-2 gap-8">
          <StatusDisplay isSafe={isSafe} />
          <CoqProofDisplay isVerified={isSafe} />
        </div>
        <LogicVisualizer isSafe={isSafe} pxlState={pxlState} />
        <Theorems />
      </div>
    </div>
  );
};

export default PxlSimulator;
