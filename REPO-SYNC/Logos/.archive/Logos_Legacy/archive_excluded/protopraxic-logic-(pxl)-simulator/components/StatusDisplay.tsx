
import React from 'react';
import CheckIcon from './icons/CheckIcon';
import XIcon from './icons/XIcon';

interface StatusDisplayProps {
  isSafe: boolean;
}

const StatusDisplay: React.FC<StatusDisplayProps> = ({ isSafe }) => {
  const bgColor = isSafe ? 'bg-green-500/10' : 'bg-red-500/10';
  const borderColor = isSafe ? 'border-green-500/50' : 'border-red-500/50';
  const textColor = isSafe ? 'text-green-400' : 'text-red-400';

  return (
    <div className={`flex flex-col items-center justify-center p-6 rounded-xl border-2 ${bgColor} ${borderColor} transition-all duration-300`}>
      <h2 className="text-lg font-semibold text-slate-300 mb-3">PXL SAFETY CHECK</h2>
      <div className={`flex items-center space-x-4 text-3xl font-bold ${textColor}`}>
        {isSafe ? <CheckIcon /> : <XIcon />}
        <span>{isSafe ? 'ACCEPTED' : 'REJECTED'}</span>
      </div>
      <p className="mt-3 text-center text-slate-400 text-sm">
        {isSafe 
          ? 'The logical state is coherent and satisfies all alignment axioms.' 
          : 'Incoherence detected. The state violates foundational principles.'}
      </p>
    </div>
  );
};

export default StatusDisplay;
