import React from 'react';
import type { PxlState } from '../types';
import ArrowRightLongIcon from './icons/ArrowRightLongIcon';

interface LogicVisualizerProps {
  pxlState: PxlState;
  isSafe: boolean;
}

const HypostasisPillar: React.FC<{ name: string; law: string; active: boolean }> = ({ name, law, active }) => {
    const baseClasses = "relative flex-1 flex flex-col items-center justify-center p-4 rounded-lg border transition-all duration-500 h-32";
    const activeClasses = "bg-cyan-900/50 border-cyan-500/80 shadow-[0_0_15px_rgba(56,189,248,0.4)]";
    const inactiveClasses = "bg-slate-800/50 border-slate-700";

    return (
        <div className={`${baseClasses} ${active ? activeClasses : inactiveClasses}`}>
            <div className={`absolute top-2 right-2 h-2 w-2 rounded-full transition-all duration-500 ${active ? 'bg-cyan-400 animate-pulse' : 'bg-slate-600'}`}></div>
            <p className="text-2xl font-bold text-cyan-400">{name}</p>
            <p className="text-sm font-semibold text-white mt-1">{law}</p>
        </div>
    );
};

const StateNode: React.FC<{ title: string, description: string, type: 'positive' | 'privative' }> = ({ title, description, type }) => {
    const positiveClasses = 'bg-cyan-900/50 border-cyan-700 text-cyan-300';
    const privativeClasses = 'bg-orange-900/50 border-orange-700 text-orange-300';
    return (
        <div className={`p-3 rounded-lg border text-center ${type === 'positive' ? positiveClasses : privativeClasses}`}>
            <h5 className="font-bold">{title}</h5>
            <p className="text-xs text-slate-400">{description}</p>
        </div>
    );
};

const TransformArrow: React.FC<{ label: string }> = ({ label }) => (
    <div className="flex flex-col items-center justify-center text-center">
        <span className="text-xs font-mono text-slate-400">{label}</span>
        <ArrowRightLongIcon />
    </div>
);


const LogicVisualizer: React.FC<LogicVisualizerProps> = ({ pxlState, isSafe }) => {
  return (
    <div className="bg-slate-800/30 p-6 rounded-xl border border-slate-700/50 shadow-lg">
      <h2 className="text-xl font-bold text-white mb-1">PXL Grounding Visualization</h2>
       <p className="text-slate-400 mb-4 text-sm">
         The three core logical laws are grounded in the interdependent hypostatic identities of the Necessary Being (𝕆).
       </p>
      
      <div className="bg-slate-900/50 p-4 rounded-xl border border-slate-700">
        <h3 className="text-center text-lg font-bold text-purple-400 mb-3">Necessary Being (𝕆)</h3>
        <div className="flex flex-col md:flex-row items-stretch justify-center gap-4">
            <HypostasisPillar name="𝕀₁" law="Identity" active={pxlState.id_hold} />
            <HypostasisPillar name="𝕀₂" law="Non-Contradiction" active={pxlState.nc_hold} />
            <HypostasisPillar name="𝕀₃" law="Excluded Middle" active={pxlState.em_hold} />
        </div>
      </div>

      {isSafe && (
        <div className="mt-4 p-4 text-center bg-slate-900/50 border border-slate-700 rounded-lg">
            <h4 className="font-bold text-cyan-400">System Integrity Loop</h4>
            <p className="text-sm text-slate-400 mb-4">The `recursive_closure` proof demonstrates that coherence is always restored.</p>
            <div className="grid grid-cols-1 md:grid-cols-9 items-center gap-2 text-slate-300">
                <StateNode title="Coherence" description="Initial State" type="positive" />
                <TransformArrow label="ϕ+" />
                <StateNode title="Existence" description="Ontological Map" type="positive" />
                <TransformArrow label="negation_of" />
                <StateNode title="Negation" description="Privative Path" type="privative" />
                <TransformArrow label="positive_counterpart" />
                <StateNode title="Existence" description="Restored State" type="positive" />
                <TransformArrow label="ϕ+⁻¹" />
                <StateNode title="Coherence" description="Loop Closed" type="positive" />
            </div>
        </div>
      )}

      {!isSafe && (
        <div className="mt-4 p-4 text-center bg-red-900/50 border border-red-500/50 rounded-lg">
            <h4 className="font-bold text-red-400">PRIVATION COLLAPSE</h4>
            <p className="text-sm text-slate-300">Incoherence leads to a collapse of logical grounding (Theorem T6). The system rejects the state to preserve integrity.</p>
        </div>
      )}

    </div>
  );
};

export default LogicVisualizer;