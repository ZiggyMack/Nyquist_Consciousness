
import React from 'react';
import type { PxlState } from '../types';

interface ControlPanelProps {
  pxlState: PxlState;
  onStateChange: (key: keyof PxlState) => void;
}

interface ToggleProps {
  label: string;
  description: string;
  enabled: boolean;
  onChange: () => void;
}

const Toggle: React.FC<ToggleProps> = ({ label, description, enabled, onChange }) => (
  <div
    onClick={onChange}
    className="flex items-center justify-between p-4 bg-slate-800/50 rounded-lg cursor-pointer transition-all duration-200 hover:bg-slate-700/50 border border-slate-700"
  >
    <div>
      <h3 className="font-semibold text-white">{label}</h3>
      <p className="text-sm text-slate-400">{description}</p>
    </div>
    <div className={`relative inline-flex items-center h-6 rounded-full w-11 transition-colors ${enabled ? 'bg-cyan-500' : 'bg-slate-600'}`}>
      <span
        className={`inline-block w-4 h-4 transform bg-white rounded-full transition-transform ${enabled ? 'translate-x-6' : 'translate-x-1'}`}
      />
    </div>
  </div>
);

const ControlPanel: React.FC<ControlPanelProps> = ({ pxlState, onStateChange }) => {
  return (
    <div className="bg-slate-800/30 p-6 rounded-xl border border-slate-700/50 shadow-lg">
      <h2 className="text-xl font-bold text-white mb-4">PXL Kernel Controls</h2>
        <div>
          <h3 className="font-semibold text-lg text-cyan-400 mb-3">Core Axioms</h3>
          <p className="text-slate-400 mb-4 text-sm">
            Toggle the foundational laws to observe the kernel's response. Coherence requires all three to hold.
          </p>
          <div className="space-y-4">
            <Toggle
              label="A1: Law of Identity"
              description="Grounded in Hypostasis 𝕀₁"
              enabled={pxlState.id_hold}
              onChange={() => onStateChange('id_hold')}
            />
            <Toggle
              label="A2: Law of Non-Contradiction"
              description="Grounded in Hypostasis 𝕀₂"
              enabled={pxlState.nc_hold}
              onChange={() => onStateChange('nc_hold')}
            />
            <Toggle
              label="A3: Law of Excluded Middle"
              description="Grounded in Hypostasis 𝕀₃"
              enabled={pxlState.em_hold}
              onChange={() => onStateChange('em_hold')}
            />
          </div>
        </div>
    </div>
  );
};

export default ControlPanel;
