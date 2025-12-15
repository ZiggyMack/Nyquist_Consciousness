
import React from 'react';
import ShieldCheckIcon from './icons/ShieldCheckIcon';
import ShieldExclamationIcon from './icons/ShieldExclamationIcon';

interface CoqProofDisplayProps {
  isVerified: boolean;
}

const CoqProofDisplay: React.FC<CoqProofDisplayProps> = ({ isVerified }) => {
  const bgColor = isVerified ? 'bg-blue-500/10' : 'bg-orange-500/10';
  const borderColor = isVerified ? 'border-blue-500/50' : 'border-orange-500/50';
  const textColor = isVerified ? 'text-blue-400' : 'text-orange-400';

  return (
    <div className={`flex flex-col items-center justify-center p-6 rounded-xl border-2 ${bgColor} ${borderColor} transition-all duration-300`}>
      <h2 className="text-lg font-semibold text-slate-300 mb-3">COQ FORMAL VERIFICATION</h2>
      <div className={`flex items-center space-x-4 text-3xl font-bold ${textColor}`}>
        {isVerified ? <ShieldCheckIcon /> : <ShieldExclamationIcon />}
        <span>{isVerified ? 'VERIFIED' : 'UNPROVABLE'}</span>
      </div>
      <p className="mt-3 text-center text-slate-400 text-sm">
        {isVerified 
          ? 'This coherent state is formally proven to be sound and safe.' 
          : 'This incoherent state is formally unprovable and leads to contradiction.'}
      </p>
      <div className="mt-2 font-mono text-xs bg-slate-900/50 p-2 rounded w-full text-center">
        {isVerified ? (
            <span className="text-green-400">Proof completed. Qed.</span>
        ) : (
            <span className="text-red-400">Error: A contradiction was found.</span>
        )}
      </div>
    </div>
  );
};

export default CoqProofDisplay;